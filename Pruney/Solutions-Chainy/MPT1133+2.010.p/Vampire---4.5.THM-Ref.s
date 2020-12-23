%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:28 EST 2020

% Result     : Theorem 7.98s
% Output     : Refutation 8.72s
% Verified   : 
% Statistics : Number of formulae       :  424 (1959 expanded)
%              Number of leaves         :   61 ( 721 expanded)
%              Depth                    :   32
%              Number of atoms          : 2028 (18127 expanded)
%              Number of equality atoms :  101 (1680 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f189,f190,f459,f1345,f1350,f1481,f1486,f2324,f3807,f3828,f3845,f3930,f3931,f3965,f6503,f6558,f6655,f6663,f6671,f6709,f6715,f6840,f8052,f8103,f8124,f8130,f8147,f8164,f8190,f8454,f8705,f9246,f11997,f12641,f12662,f13226])).

fof(f13226,plain,
    ( ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169
    | spl10_210 ),
    inference(avatar_contradiction_clause,[],[f13225])).

fof(f13225,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13224,f540])).

fof(f540,plain,(
    ! [X5] : v1_funct_2(k1_xboole_0,k1_xboole_0,X5) ),
    inference(superposition,[],[f154,f501])).

fof(f501,plain,(
    ! [X0] : k1_xboole_0 = sK9(k1_xboole_0,X0) ),
    inference(resolution,[],[f474,f127])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( sP1(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP1(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP1(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP1(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f43,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f474,plain,(
    ! [X24,X23] : ~ r2_hidden(X23,sK9(k1_xboole_0,X24)) ),
    inference(subsumption_resolution,[],[f449,f110])).

fof(f110,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f449,plain,(
    ! [X24,X23] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X23,sK9(k1_xboole_0,X24)) ) ),
    inference(resolution,[],[f163,f283])).

fof(f283,plain,(
    ! [X5] : m1_subset_1(sK9(k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f149,f173])).

fof(f173,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
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

fof(f149,plain,(
    ! [X0,X1] : m1_subset_1(sK9(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK9(X0,X1),X0,X1)
      & v1_funct_1(sK9(X0,X1))
      & v5_relat_1(sK9(X0,X1),X1)
      & v4_relat_1(sK9(X0,X1),X0)
      & v1_relat_1(sK9(X0,X1))
      & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f20,f95])).

fof(f95,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK9(X0,X1),X0,X1)
        & v1_funct_1(sK9(X0,X1))
        & v5_relat_1(sK9(X0,X1),X1)
        & v4_relat_1(sK9(X0,X1),X0)
        & v1_relat_1(sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f154,plain,(
    ! [X0,X1] : v1_funct_2(sK9(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f96])).

fof(f13224,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169
    | spl10_210 ),
    inference(forward_demodulation,[],[f13223,f501])).

fof(f13223,plain,
    ( ~ v1_funct_2(sK9(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_xboole_0,u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169
    | spl10_210 ),
    inference(forward_demodulation,[],[f13222,f8703])).

fof(f8703,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | ~ spl10_169 ),
    inference(avatar_component_clause,[],[f8701])).

fof(f8701,plain,
    ( spl10_169
  <=> k1_xboole_0 = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).

fof(f13222,plain,
    ( ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13221,f110])).

fof(f13221,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | spl10_210 ),
    inference(forward_demodulation,[],[f13220,f488])).

fof(f488,plain,(
    ! [X0] : k1_xboole_0 = sK9(X0,k1_xboole_0) ),
    inference(resolution,[],[f473,f127])).

fof(f473,plain,(
    ! [X19,X18] : ~ r2_hidden(X18,sK9(X19,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f447,f110])).

fof(f447,plain,(
    ! [X19,X18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X18,sK9(X19,k1_xboole_0)) ) ),
    inference(resolution,[],[f163,f280])).

fof(f280,plain,(
    ! [X0] : m1_subset_1(sK9(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f149,f172])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f94])).

fof(f13220,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),k1_xboole_0))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_71
    | ~ spl10_73
    | spl10_210 ),
    inference(forward_demodulation,[],[f13219,f3688])).

fof(f3688,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f3686])).

fof(f3686,plain,
    ( spl10_71
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f13219,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_73
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13218,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f111,f114])).

fof(f114,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f13218,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_73
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13217,f12228])).

fof(f12228,plain,
    ( ! [X0] :
        ( v5_pre_topc(X0,sK3,sK4)
        | ~ v1_xboole_0(X0) )
    | ~ spl10_1
    | ~ spl10_73 ),
    inference(superposition,[],[f12227,f114])).

fof(f12227,plain,
    ( v5_pre_topc(k1_xboole_0,sK3,sK4)
    | ~ spl10_1
    | ~ spl10_73 ),
    inference(forward_demodulation,[],[f183,f3701])).

fof(f3701,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f3699])).

fof(f3699,plain,
    ( spl10_73
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f183,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl10_1
  <=> v5_pre_topc(sK5,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f13217,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13216,f97])).

fof(f97,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | ~ v5_pre_topc(sK5,sK3,sK4) )
    & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | v5_pre_topc(sK5,sK3,sK4) )
    & sK5 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f71,f75,f74,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK3,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK3,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK3,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                | ~ v5_pre_topc(X2,sK3,sK4) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                | v5_pre_topc(X2,sK3,sK4) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
              | ~ v5_pre_topc(X2,sK3,sK4) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
              | v5_pre_topc(X2,sK3,sK4) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
            | ~ v5_pre_topc(sK5,sK3,sK4) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
            | v5_pre_topc(sK5,sK3,sK4) )
          & sK5 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
          | ~ v5_pre_topc(sK5,sK3,sK4) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
          | v5_pre_topc(sK5,sK3,sK4) )
        & sK5 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | ~ v5_pre_topc(sK5,sK3,sK4) )
      & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | v5_pre_topc(sK5,sK3,sK4) )
      & sK5 = sK6
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
      & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f13216,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK3)
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13215,f98])).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f13215,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13214,f99])).

fof(f99,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f13214,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl10_210 ),
    inference(subsumption_resolution,[],[f13213,f100])).

fof(f100,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f13213,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl10_210 ),
    inference(resolution,[],[f12669,f1364])).

fof(f1364,plain,(
    ! [X17,X16] :
      ( v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | ~ v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17)
      | ~ m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(subsumption_resolution,[],[f1363,f153])).

fof(f153,plain,(
    ! [X0,X1] : v1_funct_1(sK9(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

fof(f1363,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17)
      | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | ~ v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
      | ~ m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(subsumption_resolution,[],[f1357,f154])).

fof(f1357,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17)
      | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))
      | ~ v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
      | ~ m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(resolution,[],[f179,f149])).

fof(f179,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f12669,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | ~ v1_xboole_0(X0) )
    | spl10_210 ),
    inference(superposition,[],[f12526,f114])).

fof(f12526,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_210 ),
    inference(avatar_component_clause,[],[f12525])).

fof(f12525,plain,
    ( spl10_210
  <=> v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).

fof(f12662,plain,
    ( ~ spl10_206
    | spl10_2
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(avatar_split_clause,[],[f12318,f8701,f3699,f186,f12359])).

fof(f12359,plain,
    ( spl10_206
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f186,plain,
    ( spl10_2
  <=> v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f12318,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_2
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12317,f3701])).

fof(f12317,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_2
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f6557,f8703])).

fof(f6557,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_2 ),
    inference(forward_demodulation,[],[f188,f107])).

fof(f107,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f76])).

fof(f188,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f12641,plain,
    ( ~ spl10_210
    | spl10_206
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(avatar_split_clause,[],[f12640,f8701,f3699,f3686,f1324,f1320,f12359,f12525])).

fof(f1320,plain,
    ( spl10_23
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f1324,plain,
    ( spl10_24
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f12640,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f12639,f540])).

fof(f12639,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12638,f3701])).

fof(f12638,plain,
    ( ~ v1_funct_2(sK5,k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12637,f8703])).

fof(f12637,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12636,f3688])).

fof(f12636,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f12635,f111])).

fof(f12635,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12634,f3701])).

fof(f12634,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12633,f172])).

fof(f12633,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12632,f3688])).

fof(f12632,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f12631,f515])).

fof(f515,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f153,f488])).

fof(f12631,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12630,f3701])).

fof(f12630,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f12629,f516])).

fof(f516,plain,(
    ! [X5] : v1_funct_2(k1_xboole_0,X5,k1_xboole_0) ),
    inference(superposition,[],[f154,f488])).

fof(f12629,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12628,f3701])).

fof(f12628,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12627,f8703])).

fof(f12627,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12626,f3688])).

fof(f12626,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12625,f3701])).

fof(f12625,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f12079,f8703])).

fof(f12079,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_73 ),
    inference(forward_demodulation,[],[f12078,f3701])).

fof(f12078,plain,
    ( ~ v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f12077,f97])).

fof(f12077,plain,
    ( ~ v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v2_pre_topc(sK3)
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f12076,f98])).

fof(f12076,plain,
    ( ~ v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_23
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f12075,f1321])).

fof(f1321,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f12075,plain,
    ( ~ v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f6369,f1325])).

fof(f1325,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f1324])).

fof(f6369,plain,
    ( ~ v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f200,f177])).

fof(f177,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f200,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(forward_demodulation,[],[f106,f107])).

fof(f106,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f76])).

fof(f11997,plain,
    ( spl10_1
    | ~ spl10_27
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(avatar_contradiction_clause,[],[f11996])).

fof(f11996,plain,
    ( $false
    | spl10_1
    | ~ spl10_27
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f11995,f110])).

fof(f11995,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_1
    | ~ spl10_27
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f11994,f488])).

fof(f11994,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),k1_xboole_0))
    | spl10_1
    | ~ spl10_27
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f11993,f3688])).

fof(f11993,plain,
    ( ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | spl10_1
    | ~ spl10_27
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f11992,f540])).

fof(f11992,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4))
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | spl10_1
    | ~ spl10_27
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f11991,f501])).

fof(f11991,plain,
    ( ~ v1_funct_2(sK9(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_xboole_0,u1_struct_0(sK4))
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | spl10_1
    | ~ spl10_27
    | ~ spl10_73
    | ~ spl10_169 ),
    inference(forward_demodulation,[],[f11990,f8703])).

fof(f11990,plain,
    ( ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | spl10_1
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f11989,f193])).

fof(f11989,plain,
    ( ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | spl10_1
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f11988,f8347])).

fof(f8347,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK3,sK4)
        | ~ v1_xboole_0(X0) )
    | spl10_1
    | ~ spl10_73 ),
    inference(superposition,[],[f3730,f114])).

fof(f3730,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK3,sK4)
    | spl10_1
    | ~ spl10_73 ),
    inference(backward_demodulation,[],[f184,f3701])).

fof(f184,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f182])).

fof(f11988,plain,
    ( v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f11987,f97])).

fof(f11987,plain,
    ( v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK3)
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f11986,f98])).

fof(f11986,plain,
    ( v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f11985,f99])).

fof(f11985,plain,
    ( v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f11960,f100])).

fof(f11960,plain,
    ( v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4)
    | ~ m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(resolution,[],[f1477,f9255])).

fof(f9255,plain,
    ( ! [X0] :
        ( v5_pre_topc(X0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | ~ v1_xboole_0(X0) )
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(superposition,[],[f9247,f114])).

fof(f9247,plain,
    ( v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_27
    | ~ spl10_73 ),
    inference(forward_demodulation,[],[f1338,f3701])).

fof(f1338,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1336,plain,
    ( spl10_27
  <=> v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f1477,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17)
      | ~ m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(subsumption_resolution,[],[f1476,f153])).

fof(f1476,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17)
      | ~ v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
      | ~ m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(subsumption_resolution,[],[f1442,f154])).

fof(f1442,plain,(
    ! [X17,X16] :
      ( ~ v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17)
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))
      | ~ v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))))
      | ~ m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16) ) ),
    inference(resolution,[],[f180,f149])).

fof(f180,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f9246,plain,
    ( spl10_26
    | ~ spl10_71
    | ~ spl10_73 ),
    inference(avatar_contradiction_clause,[],[f9245])).

fof(f9245,plain,
    ( $false
    | spl10_26
    | ~ spl10_71
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f9244,f111])).

fof(f9244,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl10_26
    | ~ spl10_71
    | ~ spl10_73 ),
    inference(forward_demodulation,[],[f9243,f3701])).

fof(f9243,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | spl10_26
    | ~ spl10_71 ),
    inference(forward_demodulation,[],[f9242,f172])).

fof(f9242,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | spl10_26
    | ~ spl10_71 ),
    inference(forward_demodulation,[],[f1334,f3688])).

fof(f1334,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | spl10_26 ),
    inference(avatar_component_clause,[],[f1332])).

fof(f1332,plain,
    ( spl10_26
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f8705,plain,
    ( spl10_169
    | ~ spl10_15
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f8693,f3840,f454,f8701])).

fof(f454,plain,
    ( spl10_15
  <=> ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f3840,plain,
    ( spl10_76
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f8693,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | ~ spl10_15
    | ~ spl10_76 ),
    inference(resolution,[],[f8632,f587])).

fof(f587,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl10_15 ),
    inference(resolution,[],[f481,f127])).

fof(f481,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ r1_tarski(X2,k1_xboole_0) )
    | ~ spl10_15 ),
    inference(resolution,[],[f455,f141])).

fof(f141,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f89,f90])).

fof(f90,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f455,plain,
    ( ! [X7] : ~ r2_hidden(X7,k1_xboole_0)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f454])).

fof(f8632,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK3),X0)
    | ~ spl10_76 ),
    inference(resolution,[],[f3842,f2345])).

fof(f2345,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2344,f291])).

fof(f291,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f155,f111])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2344,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_partfun1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f2336,f400])).

fof(f400,plain,(
    ! [X5] : v4_relat_1(k1_xboole_0,X5) ),
    inference(resolution,[],[f158,f111])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2336,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_partfun1(k1_xboole_0,X0)
      | ~ v4_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f2232,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f2232,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f2183,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2183,plain,(
    ! [X10] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X10)) ),
    inference(resolution,[],[f904,f111])).

fof(f904,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f903])).

fof(f903,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f157,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f3842,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK3))
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f3840])).

fof(f8454,plain,
    ( spl10_76
    | ~ spl10_73
    | ~ spl10_79 ),
    inference(avatar_split_clause,[],[f8410,f3894,f3699,f3840])).

fof(f3894,plain,
    ( spl10_79
  <=> v1_partfun1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f8410,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK3))
    | ~ spl10_73
    | ~ spl10_79 ),
    inference(backward_demodulation,[],[f3896,f3701])).

fof(f3896,plain,
    ( v1_partfun1(sK5,u1_struct_0(sK3))
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f3894])).

fof(f8190,plain,
    ( spl10_73
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f868,f464,f3699])).

fof(f464,plain,
    ( spl10_18
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f868,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f857,f201])).

fof(f201,plain,(
    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) ),
    inference(resolution,[],[f144,f103])).

fof(f103,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f857,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f439,f127])).

fof(f439,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f163,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f8164,plain,
    ( spl10_73
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f4019,f2014,f3699])).

fof(f2014,plain,
    ( spl10_34
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f4019,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f4014,f110])).

fof(f4014,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK5
    | ~ spl10_34 ),
    inference(resolution,[],[f2015,f857])).

fof(f2015,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f2014])).

fof(f8147,plain,
    ( spl10_34
    | ~ spl10_71 ),
    inference(avatar_split_clause,[],[f7338,f3686,f2014])).

fof(f7338,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl10_71 ),
    inference(forward_demodulation,[],[f7305,f172])).

fof(f7305,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))
    | ~ spl10_71 ),
    inference(backward_demodulation,[],[f202,f3688])).

fof(f202,plain,(
    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    inference(resolution,[],[f144,f200])).

fof(f8130,plain,
    ( spl10_6
    | spl10_69
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f8129,f3899,f3669,f228])).

fof(f228,plain,
    ( spl10_6
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f3669,plain,
    ( spl10_69
  <=> v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f3899,plain,
    ( spl10_80
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f8129,plain,
    ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f8128,f198])).

fof(f198,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(forward_demodulation,[],[f105,f107])).

fof(f105,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f8128,plain,
    ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f5511,f3900])).

fof(f3900,plain,
    ( v1_funct_1(sK5)
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f3899])).

fof(f5511,plain,
    ( ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(resolution,[],[f1051,f202])).

fof(f1051,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X6,X7))
      | ~ v1_funct_1(X5)
      | v1_partfun1(X5,X6)
      | v1_xboole_0(X7)
      | ~ v1_funct_2(X5,X6,X7) ) ),
    inference(resolution,[],[f130,f145])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f8124,plain,
    ( spl10_69
    | spl10_71
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f8123,f3899,f3686,f3669])).

fof(f8123,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f8122,f3900])).

fof(f8122,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f6377,f198])).

fof(f6377,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f200,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f8103,plain,
    ( ~ spl10_69
    | spl10_30
    | ~ spl10_79
    | ~ spl10_81
    | ~ spl10_109 ),
    inference(avatar_split_clause,[],[f8102,f6732,f3903,f3894,f1464,f3669])).

fof(f1464,plain,
    ( spl10_30
  <=> v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f3903,plain,
    ( spl10_81
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f6732,plain,
    ( spl10_109
  <=> v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).

fof(f8102,plain,
    ( ~ v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | spl10_30
    | ~ spl10_79
    | ~ spl10_81
    | ~ spl10_109 ),
    inference(subsumption_resolution,[],[f7876,f6733])).

fof(f6733,plain,
    ( v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl10_109 ),
    inference(avatar_component_clause,[],[f6732])).

fof(f7876,plain,
    ( ~ v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | spl10_30
    | ~ spl10_79
    | ~ spl10_81 ),
    inference(resolution,[],[f7639,f1466])).

fof(f1466,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | spl10_30 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f7639,plain,
    ( ! [X37] :
        ( v1_funct_2(sK5,X37,u1_struct_0(sK4))
        | ~ v1_partfun1(sK5,X37)
        | ~ v4_relat_1(sK5,X37) )
    | ~ spl10_79
    | ~ spl10_81 ),
    inference(superposition,[],[f3904,f5730])).

fof(f5730,plain,
    ( ! [X18] :
        ( u1_struct_0(sK3) = X18
        | ~ v1_partfun1(sK5,X18)
        | ~ v4_relat_1(sK5,X18) )
    | ~ spl10_79 ),
    inference(subsumption_resolution,[],[f5729,f292])).

fof(f292,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f155,f103])).

fof(f5729,plain,
    ( ! [X18] :
        ( u1_struct_0(sK3) = X18
        | ~ v1_relat_1(sK5)
        | ~ v1_partfun1(sK5,X18)
        | ~ v4_relat_1(sK5,X18) )
    | ~ spl10_79 ),
    inference(subsumption_resolution,[],[f5709,f401])).

fof(f401,plain,(
    v4_relat_1(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f158,f103])).

fof(f5709,plain,
    ( ! [X18] :
        ( u1_struct_0(sK3) = X18
        | ~ v4_relat_1(sK5,u1_struct_0(sK3))
        | ~ v1_relat_1(sK5)
        | ~ v1_partfun1(sK5,X18)
        | ~ v4_relat_1(sK5,X18) )
    | ~ spl10_79 ),
    inference(resolution,[],[f814,f3896])).

fof(f814,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X2)
      | X1 = X2
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f808])).

fof(f808,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v1_partfun1(X0,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f139,f139])).

fof(f3904,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl10_81 ),
    inference(avatar_component_clause,[],[f3903])).

fof(f8052,plain,
    ( ~ spl10_25
    | ~ spl10_26
    | spl10_27
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_80
    | ~ spl10_104 ),
    inference(avatar_split_clause,[],[f8051,f6513,f3899,f1324,f1320,f1336,f1332,f1328])).

fof(f1328,plain,
    ( spl10_25
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f6513,plain,
    ( spl10_104
  <=> v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f8051,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_80
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f8050,f97])).

fof(f8050,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v2_pre_topc(sK3)
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_80
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f8049,f98])).

fof(f8049,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_80
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f8048,f1321])).

fof(f8048,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_24
    | ~ spl10_80
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f8047,f1325])).

fof(f8047,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_80
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f8046,f3900])).

fof(f8046,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f8045,f198])).

fof(f8045,plain,
    ( v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f6368,f6515])).

fof(f6515,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f6513])).

fof(f6368,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f200,f178])).

fof(f178,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f6840,plain,(
    spl10_109 ),
    inference(avatar_split_clause,[],[f6375,f6732])).

fof(f6375,plain,(
    v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(resolution,[],[f200,f158])).

fof(f6715,plain,
    ( ~ spl10_30
    | spl10_104
    | ~ spl10_32
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f6714,f3899,f1468,f1460,f1456,f1472,f6513,f1464])).

fof(f1472,plain,
    ( spl10_32
  <=> v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f1456,plain,
    ( spl10_28
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f1460,plain,
    ( spl10_29
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f1468,plain,
    ( spl10_31
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f6714,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6713,f1457])).

fof(f1457,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f6713,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6712,f1461])).

fof(f1461,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f6712,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6711,f99])).

fof(f6711,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6710,f100])).

fof(f6710,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6506,f1469])).

fof(f1469,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f6506,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6505,f3900])).

fof(f6505,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f6371,f198])).

fof(f6371,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f200,f179])).

fof(f6709,plain,
    ( ~ spl10_30
    | spl10_32
    | ~ spl10_104
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f6708,f3899,f1468,f1460,f1456,f6513,f1472,f1464])).

fof(f6708,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6707,f1457])).

fof(f6707,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6706,f1461])).

fof(f6706,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6705,f99])).

fof(f6705,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6704,f100])).

fof(f6704,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6518,f1469])).

fof(f6518,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6517,f3900])).

fof(f6517,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f6370,f198])).

fof(f6370,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f200,f180])).

fof(f6671,plain,
    ( ~ spl10_30
    | spl10_32
    | ~ spl10_1
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(avatar_split_clause,[],[f6670,f3903,f3899,f1468,f182,f1472,f1464])).

fof(f6670,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6669,f97])).

fof(f6669,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6668,f98])).

fof(f6668,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6667,f99])).

fof(f6667,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6666,f100])).

fof(f6666,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6665,f3904])).

fof(f6665,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6664,f103])).

fof(f6664,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6591,f3900])).

fof(f6591,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31 ),
    inference(resolution,[],[f1469,f177])).

fof(f6663,plain,
    ( ~ spl10_30
    | spl10_1
    | ~ spl10_32
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(avatar_split_clause,[],[f6662,f3903,f3899,f1468,f1472,f182,f1464])).

fof(f6662,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6661,f97])).

fof(f6661,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6660,f98])).

fof(f6660,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6659,f99])).

fof(f6659,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6658,f100])).

fof(f6658,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80
    | ~ spl10_81 ),
    inference(subsumption_resolution,[],[f6657,f3904])).

fof(f6657,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6656,f103])).

fof(f6656,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f6590,f3900])).

fof(f6590,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_31 ),
    inference(resolution,[],[f1469,f178])).

fof(f6655,plain,
    ( spl10_104
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f6654,f186,f6513])).

fof(f6654,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f187,f107])).

fof(f187,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f6558,plain,
    ( ~ spl10_104
    | spl10_2 ),
    inference(avatar_split_clause,[],[f6557,f186,f6513])).

fof(f6503,plain,(
    spl10_31 ),
    inference(avatar_contradiction_clause,[],[f6494])).

fof(f6494,plain,
    ( $false
    | spl10_31 ),
    inference(subsumption_resolution,[],[f103,f6468])).

fof(f6468,plain,
    ( ! [X0] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK4))))
    | spl10_31 ),
    inference(subsumption_resolution,[],[f6460,f2208])).

fof(f2208,plain,(
    r1_tarski(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(resolution,[],[f2186,f144])).

fof(f2186,plain,(
    m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) ),
    inference(resolution,[],[f904,f200])).

fof(f6460,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK4)))) )
    | spl10_31 ),
    inference(resolution,[],[f1470,f164])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f1470,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | spl10_31 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f3965,plain,
    ( spl10_79
    | ~ spl10_81
    | spl10_3
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f3964,f3899,f214,f3903,f3894])).

fof(f214,plain,
    ( spl10_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f3964,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_partfun1(sK5,u1_struct_0(sK3))
    | spl10_3
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f3963,f216])).

fof(f216,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f214])).

fof(f3963,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_partfun1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f3943,f3900])).

fof(f3943,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f103,f130])).

fof(f3931,plain,(
    spl10_80 ),
    inference(avatar_split_clause,[],[f101,f3899])).

fof(f101,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

fof(f3930,plain,(
    spl10_81 ),
    inference(avatar_split_clause,[],[f102,f3903])).

fof(f102,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f76])).

fof(f3845,plain,
    ( ~ spl10_3
    | spl10_18 ),
    inference(avatar_split_clause,[],[f477,f464,f214])).

fof(f477,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_18 ),
    inference(duplicate_literal_removal,[],[f476])).

fof(f476,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_18 ),
    inference(superposition,[],[f466,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f172,f114])).

fof(f466,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f464])).

fof(f3828,plain,
    ( ~ spl10_3
    | spl10_30
    | ~ spl10_73 ),
    inference(avatar_split_clause,[],[f3827,f3699,f1464,f214])).

fof(f3827,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_30
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f3826,f110])).

fof(f3826,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_30
    | ~ spl10_73 ),
    inference(forward_demodulation,[],[f1863,f3701])).

fof(f1863,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_xboole_0(sK5)
    | spl10_30 ),
    inference(resolution,[],[f701,f1466])).

fof(f701,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f675,f114])).

fof(f675,plain,(
    ! [X10,X11] :
      ( v1_funct_2(k1_xboole_0,X10,X11)
      | ~ v1_xboole_0(X11) ) ),
    inference(superposition,[],[f154,f594])).

fof(f594,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK9(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f450,f127])).

fof(f450,plain,(
    ! [X17,X15,X16] :
      ( ~ r2_hidden(X16,sK9(X17,X15))
      | ~ v1_xboole_0(X15) ) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,(
    ! [X17,X15,X16] :
      ( ~ v1_xboole_0(X15)
      | ~ r2_hidden(X16,sK9(X17,X15))
      | ~ v1_xboole_0(X15) ) ),
    inference(resolution,[],[f163,f282])).

fof(f282,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK9(X3,X4),k1_zfmisc_1(X4))
      | ~ v1_xboole_0(X4) ) ),
    inference(superposition,[],[f149,f195])).

fof(f3807,plain,
    ( ~ spl10_6
    | spl10_25
    | ~ spl10_73 ),
    inference(avatar_split_clause,[],[f3806,f3699,f1328,f228])).

fof(f3806,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | spl10_25
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f3805,f110])).

fof(f3805,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | spl10_25
    | ~ spl10_73 ),
    inference(forward_demodulation,[],[f1862,f3701])).

fof(f1862,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_xboole_0(sK5)
    | spl10_25 ),
    inference(resolution,[],[f701,f1330])).

fof(f1330,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | spl10_25 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f2324,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f2313])).

fof(f2313,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f110,f458])).

fof(f458,plain,
    ( ! [X6] : ~ v1_xboole_0(X6)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl10_16
  <=> ! [X6] : ~ v1_xboole_0(X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f1486,plain,(
    spl10_29 ),
    inference(avatar_contradiction_clause,[],[f1485])).

fof(f1485,plain,
    ( $false
    | spl10_29 ),
    inference(subsumption_resolution,[],[f1482,f98])).

fof(f1482,plain,
    ( ~ l1_pre_topc(sK3)
    | spl10_29 ),
    inference(resolution,[],[f1462,f373])).

fof(f373,plain,(
    ! [X5] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f134,f112])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f1462,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | spl10_29 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f1481,plain,(
    spl10_28 ),
    inference(avatar_contradiction_clause,[],[f1480])).

fof(f1480,plain,
    ( $false
    | spl10_28 ),
    inference(subsumption_resolution,[],[f1479,f97])).

fof(f1479,plain,
    ( ~ v2_pre_topc(sK3)
    | spl10_28 ),
    inference(subsumption_resolution,[],[f1478,f98])).

fof(f1478,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl10_28 ),
    inference(resolution,[],[f1458,f120])).

fof(f120,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f1458,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | spl10_28 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f1350,plain,(
    spl10_24 ),
    inference(avatar_contradiction_clause,[],[f1349])).

fof(f1349,plain,
    ( $false
    | spl10_24 ),
    inference(subsumption_resolution,[],[f1346,f100])).

fof(f1346,plain,
    ( ~ l1_pre_topc(sK4)
    | spl10_24 ),
    inference(resolution,[],[f1326,f373])).

fof(f1326,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_24 ),
    inference(avatar_component_clause,[],[f1324])).

fof(f1345,plain,(
    spl10_23 ),
    inference(avatar_contradiction_clause,[],[f1344])).

fof(f1344,plain,
    ( $false
    | spl10_23 ),
    inference(subsumption_resolution,[],[f1343,f99])).

fof(f1343,plain,
    ( ~ v2_pre_topc(sK4)
    | spl10_23 ),
    inference(subsumption_resolution,[],[f1342,f100])).

fof(f1342,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | spl10_23 ),
    inference(resolution,[],[f1322,f120])).

fof(f1322,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl10_23 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f459,plain,
    ( spl10_15
    | spl10_16 ),
    inference(avatar_split_clause,[],[f441,f457,f454])).

fof(f441,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X6)
      | ~ r2_hidden(X7,k1_xboole_0) ) ),
    inference(resolution,[],[f163,f111])).

fof(f190,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f108,f186,f182])).

fof(f108,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f189,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f109,f186,f182])).

fof(f109,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:56:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (32605)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (32605)Refutation not found, incomplete strategy% (32605)------------------------------
% 0.22/0.51  % (32605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32613)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (32607)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (32617)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (32605)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32605)Memory used [KB]: 2046
% 0.22/0.52  % (32605)Time elapsed: 0.080 s
% 0.22/0.52  % (32605)------------------------------
% 0.22/0.52  % (32605)------------------------------
% 0.22/0.52  % (32634)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (32610)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (32627)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (32624)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (32606)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (32609)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (32611)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (32619)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (32626)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (32608)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (32633)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (32620)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (32626)Refutation not found, incomplete strategy% (32626)------------------------------
% 0.22/0.55  % (32626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32626)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32626)Memory used [KB]: 1791
% 0.22/0.55  % (32626)Time elapsed: 0.106 s
% 0.22/0.55  % (32626)------------------------------
% 0.22/0.55  % (32626)------------------------------
% 0.22/0.55  % (32622)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (32622)Refutation not found, incomplete strategy% (32622)------------------------------
% 0.22/0.55  % (32622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32622)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32622)Memory used [KB]: 10746
% 0.22/0.55  % (32622)Time elapsed: 0.136 s
% 0.22/0.55  % (32622)------------------------------
% 0.22/0.55  % (32622)------------------------------
% 0.22/0.55  % (32632)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (32625)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (32631)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (32630)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (32615)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (32618)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (32616)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (32615)Refutation not found, incomplete strategy% (32615)------------------------------
% 0.22/0.56  % (32615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32627)Refutation not found, incomplete strategy% (32627)------------------------------
% 0.22/0.56  % (32627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32614)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (32628)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (32629)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (32623)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.58  % (32615)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (32615)Memory used [KB]: 10874
% 0.22/0.58  % (32615)Time elapsed: 0.156 s
% 0.22/0.58  % (32615)------------------------------
% 0.22/0.58  % (32615)------------------------------
% 0.22/0.58  % (32627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (32627)Memory used [KB]: 11001
% 0.22/0.58  % (32627)Time elapsed: 0.146 s
% 0.22/0.58  % (32627)------------------------------
% 0.22/0.58  % (32627)------------------------------
% 0.22/0.58  % (32625)Refutation not found, incomplete strategy% (32625)------------------------------
% 0.22/0.58  % (32625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (32625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (32625)Memory used [KB]: 10874
% 0.22/0.58  % (32625)Time elapsed: 0.168 s
% 0.22/0.58  % (32625)------------------------------
% 0.22/0.58  % (32625)------------------------------
% 0.22/0.58  % (32621)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (32612)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.59  % (32616)Refutation not found, incomplete strategy% (32616)------------------------------
% 0.22/0.59  % (32616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (32616)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (32616)Memory used [KB]: 10874
% 0.22/0.59  % (32616)Time elapsed: 0.173 s
% 0.22/0.59  % (32616)------------------------------
% 0.22/0.59  % (32616)------------------------------
% 1.79/0.59  % (32614)Refutation not found, incomplete strategy% (32614)------------------------------
% 1.79/0.59  % (32614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.59  % (32614)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.59  
% 1.79/0.59  % (32614)Memory used [KB]: 10874
% 1.79/0.59  % (32614)Time elapsed: 0.154 s
% 1.79/0.59  % (32614)------------------------------
% 1.79/0.59  % (32614)------------------------------
% 2.06/0.63  % (32635)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.06/0.69  % (32637)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.06/0.69  % (32636)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.65/0.73  % (32640)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.65/0.74  % (32642)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.65/0.75  % (32638)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.65/0.76  % (32639)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.65/0.78  % (32641)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.12/0.80  % (32639)Refutation not found, incomplete strategy% (32639)------------------------------
% 3.12/0.80  % (32639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.81  % (32639)Termination reason: Refutation not found, incomplete strategy
% 3.12/0.81  
% 3.12/0.81  % (32639)Memory used [KB]: 11001
% 3.12/0.81  % (32639)Time elapsed: 0.152 s
% 3.12/0.81  % (32639)------------------------------
% 3.12/0.81  % (32639)------------------------------
% 3.12/0.82  % (32636)Refutation not found, incomplete strategy% (32636)------------------------------
% 3.12/0.82  % (32636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.82  % (32636)Termination reason: Refutation not found, incomplete strategy
% 3.12/0.82  
% 3.12/0.82  % (32636)Memory used [KB]: 6268
% 3.12/0.82  % (32636)Time elapsed: 0.204 s
% 3.12/0.82  % (32636)------------------------------
% 3.12/0.82  % (32636)------------------------------
% 3.12/0.84  % (32610)Time limit reached!
% 3.12/0.84  % (32610)------------------------------
% 3.12/0.84  % (32610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.84  % (32610)Termination reason: Time limit
% 3.12/0.84  
% 3.12/0.84  % (32610)Memory used [KB]: 8955
% 3.12/0.84  % (32610)Time elapsed: 0.402 s
% 3.12/0.84  % (32610)------------------------------
% 3.12/0.84  % (32610)------------------------------
% 3.96/0.92  % (32617)Time limit reached!
% 3.96/0.92  % (32617)------------------------------
% 3.96/0.92  % (32617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.92  % (32617)Termination reason: Time limit
% 3.96/0.92  
% 3.96/0.92  % (32617)Memory used [KB]: 7931
% 3.96/0.92  % (32617)Time elapsed: 0.507 s
% 3.96/0.92  % (32617)------------------------------
% 3.96/0.92  % (32617)------------------------------
% 3.96/0.92  % (32606)Time limit reached!
% 3.96/0.92  % (32606)------------------------------
% 3.96/0.92  % (32606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.92  % (32606)Termination reason: Time limit
% 3.96/0.92  
% 3.96/0.92  % (32606)Memory used [KB]: 6908
% 3.96/0.92  % (32606)Time elapsed: 0.507 s
% 3.96/0.92  % (32606)------------------------------
% 3.96/0.92  % (32606)------------------------------
% 4.08/0.95  % (32643)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.08/0.96  % (32645)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.08/0.98  % (32644)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.08/1.01  % (32633)Time limit reached!
% 4.08/1.01  % (32633)------------------------------
% 4.08/1.01  % (32633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.02  % (32621)Time limit reached!
% 4.65/1.02  % (32621)------------------------------
% 4.65/1.02  % (32621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.02  % (32621)Termination reason: Time limit
% 4.65/1.02  
% 4.65/1.02  % (32621)Memory used [KB]: 14456
% 4.65/1.02  % (32621)Time elapsed: 0.603 s
% 4.65/1.02  % (32621)------------------------------
% 4.65/1.02  % (32621)------------------------------
% 4.65/1.02  % (32633)Termination reason: Time limit
% 4.65/1.02  % (32633)Termination phase: Saturation
% 4.65/1.02  
% 4.65/1.02  % (32633)Memory used [KB]: 7164
% 4.65/1.02  % (32633)Time elapsed: 0.600 s
% 4.65/1.02  % (32633)------------------------------
% 4.65/1.02  % (32633)------------------------------
% 4.65/1.02  % (32638)Time limit reached!
% 4.65/1.02  % (32638)------------------------------
% 4.65/1.02  % (32638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.02  % (32638)Termination reason: Time limit
% 4.65/1.02  
% 4.65/1.02  % (32638)Memory used [KB]: 6908
% 4.65/1.02  % (32638)Time elapsed: 0.410 s
% 4.65/1.02  % (32638)------------------------------
% 4.65/1.02  % (32638)------------------------------
% 4.65/1.04  % (32612)Time limit reached!
% 4.65/1.04  % (32612)------------------------------
% 4.65/1.04  % (32612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.04  % (32612)Termination reason: Time limit
% 4.65/1.04  % (32612)Termination phase: Saturation
% 4.65/1.04  
% 4.65/1.04  % (32612)Memory used [KB]: 11129
% 4.65/1.04  % (32612)Time elapsed: 0.600 s
% 4.65/1.04  % (32612)------------------------------
% 4.65/1.04  % (32612)------------------------------
% 4.65/1.06  % (32646)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.13/1.11  % (32650)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.13/1.13  % (32647)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.13/1.15  % (32649)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.13/1.15  % (32648)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.13/1.16  % (32651)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 7.98/1.44  % (32607)Time limit reached!
% 7.98/1.44  % (32607)------------------------------
% 7.98/1.44  % (32607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.98/1.44  % (32607)Termination reason: Time limit
% 7.98/1.44  
% 7.98/1.44  % (32607)Memory used [KB]: 17782
% 7.98/1.44  % (32607)Time elapsed: 1.027 s
% 7.98/1.44  % (32607)------------------------------
% 7.98/1.44  % (32607)------------------------------
% 7.98/1.45  % (32632)Refutation found. Thanks to Tanya!
% 7.98/1.45  % SZS status Theorem for theBenchmark
% 7.98/1.45  % SZS output start Proof for theBenchmark
% 8.72/1.48  fof(f13227,plain,(
% 8.72/1.48    $false),
% 8.72/1.48    inference(avatar_sat_refutation,[],[f189,f190,f459,f1345,f1350,f1481,f1486,f2324,f3807,f3828,f3845,f3930,f3931,f3965,f6503,f6558,f6655,f6663,f6671,f6709,f6715,f6840,f8052,f8103,f8124,f8130,f8147,f8164,f8190,f8454,f8705,f9246,f11997,f12641,f12662,f13226])).
% 8.72/1.48  fof(f13226,plain,(
% 8.72/1.48    ~spl10_1 | ~spl10_71 | ~spl10_73 | ~spl10_169 | spl10_210),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f13225])).
% 8.72/1.48  fof(f13225,plain,(
% 8.72/1.48    $false | (~spl10_1 | ~spl10_71 | ~spl10_73 | ~spl10_169 | spl10_210)),
% 8.72/1.48    inference(subsumption_resolution,[],[f13224,f540])).
% 8.72/1.48  fof(f540,plain,(
% 8.72/1.48    ( ! [X5] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X5)) )),
% 8.72/1.48    inference(superposition,[],[f154,f501])).
% 8.72/1.48  fof(f501,plain,(
% 8.72/1.48    ( ! [X0] : (k1_xboole_0 = sK9(k1_xboole_0,X0)) )),
% 8.72/1.48    inference(resolution,[],[f474,f127])).
% 8.72/1.48  fof(f127,plain,(
% 8.72/1.48    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 8.72/1.48    inference(cnf_transformation,[],[f83])).
% 8.72/1.48  fof(f83,plain,(
% 8.72/1.48    ! [X0] : ((sP1(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 8.72/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f82])).
% 8.72/1.48  fof(f82,plain,(
% 8.72/1.48    ! [X0] : (? [X1] : (sP1(X1,X0) & r2_hidden(X1,X0)) => (sP1(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f67,plain,(
% 8.72/1.48    ! [X0] : (? [X1] : (sP1(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 8.72/1.48    inference(definition_folding,[],[f43,f66])).
% 8.72/1.48  fof(f66,plain,(
% 8.72/1.48    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP1(X1,X0))),
% 8.72/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 8.72/1.48  fof(f43,plain,(
% 8.72/1.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 8.72/1.48    inference(ennf_transformation,[],[f16])).
% 8.72/1.48  fof(f16,axiom,(
% 8.72/1.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 8.72/1.48  fof(f474,plain,(
% 8.72/1.48    ( ! [X24,X23] : (~r2_hidden(X23,sK9(k1_xboole_0,X24))) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f449,f110])).
% 8.72/1.48  fof(f110,plain,(
% 8.72/1.48    v1_xboole_0(k1_xboole_0)),
% 8.72/1.48    inference(cnf_transformation,[],[f2])).
% 8.72/1.48  fof(f2,axiom,(
% 8.72/1.48    v1_xboole_0(k1_xboole_0)),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 8.72/1.48  fof(f449,plain,(
% 8.72/1.48    ( ! [X24,X23] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X23,sK9(k1_xboole_0,X24))) )),
% 8.72/1.48    inference(resolution,[],[f163,f283])).
% 8.72/1.48  fof(f283,plain,(
% 8.72/1.48    ( ! [X5] : (m1_subset_1(sK9(k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0))) )),
% 8.72/1.48    inference(superposition,[],[f149,f173])).
% 8.72/1.48  fof(f173,plain,(
% 8.72/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 8.72/1.48    inference(equality_resolution,[],[f147])).
% 8.72/1.48  fof(f147,plain,(
% 8.72/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 8.72/1.48    inference(cnf_transformation,[],[f94])).
% 8.72/1.48  fof(f94,plain,(
% 8.72/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 8.72/1.48    inference(flattening,[],[f93])).
% 8.72/1.48  fof(f93,plain,(
% 8.72/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 8.72/1.48    inference(nnf_transformation,[],[f4])).
% 8.72/1.48  fof(f4,axiom,(
% 8.72/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 8.72/1.48  fof(f149,plain,(
% 8.72/1.48    ( ! [X0,X1] : (m1_subset_1(sK9(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f96])).
% 8.72/1.48  fof(f96,plain,(
% 8.72/1.48    ! [X0,X1] : (v1_funct_2(sK9(X0,X1),X0,X1) & v1_funct_1(sK9(X0,X1)) & v5_relat_1(sK9(X0,X1),X1) & v4_relat_1(sK9(X0,X1),X0) & v1_relat_1(sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.72/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f20,f95])).
% 8.72/1.48  fof(f95,plain,(
% 8.72/1.48    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK9(X0,X1),X0,X1) & v1_funct_1(sK9(X0,X1)) & v5_relat_1(sK9(X0,X1),X1) & v4_relat_1(sK9(X0,X1),X0) & v1_relat_1(sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f20,axiom,(
% 8.72/1.48    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 8.72/1.48  fof(f163,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f61])).
% 8.72/1.48  fof(f61,plain,(
% 8.72/1.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.72/1.48    inference(ennf_transformation,[],[f8])).
% 8.72/1.48  fof(f8,axiom,(
% 8.72/1.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 8.72/1.48  fof(f154,plain,(
% 8.72/1.48    ( ! [X0,X1] : (v1_funct_2(sK9(X0,X1),X0,X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f96])).
% 8.72/1.48  fof(f13224,plain,(
% 8.72/1.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) | (~spl10_1 | ~spl10_71 | ~spl10_73 | ~spl10_169 | spl10_210)),
% 8.72/1.48    inference(forward_demodulation,[],[f13223,f501])).
% 8.72/1.48  fof(f13223,plain,(
% 8.72/1.48    ~v1_funct_2(sK9(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_xboole_0,u1_struct_0(sK4)) | (~spl10_1 | ~spl10_71 | ~spl10_73 | ~spl10_169 | spl10_210)),
% 8.72/1.48    inference(forward_demodulation,[],[f13222,f8703])).
% 8.72/1.48  fof(f8703,plain,(
% 8.72/1.48    k1_xboole_0 = u1_struct_0(sK3) | ~spl10_169),
% 8.72/1.48    inference(avatar_component_clause,[],[f8701])).
% 8.72/1.48  fof(f8701,plain,(
% 8.72/1.48    spl10_169 <=> k1_xboole_0 = u1_struct_0(sK3)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).
% 8.72/1.48  fof(f13222,plain,(
% 8.72/1.48    ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | (~spl10_1 | ~spl10_71 | ~spl10_73 | spl10_210)),
% 8.72/1.48    inference(subsumption_resolution,[],[f13221,f110])).
% 8.72/1.48  fof(f13221,plain,(
% 8.72/1.48    ~v1_xboole_0(k1_xboole_0) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | (~spl10_1 | ~spl10_71 | ~spl10_73 | spl10_210)),
% 8.72/1.48    inference(forward_demodulation,[],[f13220,f488])).
% 8.72/1.48  fof(f488,plain,(
% 8.72/1.48    ( ! [X0] : (k1_xboole_0 = sK9(X0,k1_xboole_0)) )),
% 8.72/1.48    inference(resolution,[],[f473,f127])).
% 8.72/1.48  fof(f473,plain,(
% 8.72/1.48    ( ! [X19,X18] : (~r2_hidden(X18,sK9(X19,k1_xboole_0))) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f447,f110])).
% 8.72/1.48  fof(f447,plain,(
% 8.72/1.48    ( ! [X19,X18] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X18,sK9(X19,k1_xboole_0))) )),
% 8.72/1.48    inference(resolution,[],[f163,f280])).
% 8.72/1.48  fof(f280,plain,(
% 8.72/1.48    ( ! [X0] : (m1_subset_1(sK9(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 8.72/1.48    inference(superposition,[],[f149,f172])).
% 8.72/1.48  fof(f172,plain,(
% 8.72/1.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 8.72/1.48    inference(equality_resolution,[],[f148])).
% 8.72/1.48  fof(f148,plain,(
% 8.72/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 8.72/1.48    inference(cnf_transformation,[],[f94])).
% 8.72/1.48  fof(f13220,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),k1_xboole_0)) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | (~spl10_1 | ~spl10_71 | ~spl10_73 | spl10_210)),
% 8.72/1.48    inference(forward_demodulation,[],[f13219,f3688])).
% 8.72/1.48  fof(f3688,plain,(
% 8.72/1.48    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_71),
% 8.72/1.48    inference(avatar_component_clause,[],[f3686])).
% 8.72/1.48  fof(f3686,plain,(
% 8.72/1.48    spl10_71 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).
% 8.72/1.48  fof(f13219,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | (~spl10_1 | ~spl10_73 | spl10_210)),
% 8.72/1.48    inference(subsumption_resolution,[],[f13218,f193])).
% 8.72/1.48  fof(f193,plain,(
% 8.72/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 8.72/1.48    inference(superposition,[],[f111,f114])).
% 8.72/1.48  fof(f114,plain,(
% 8.72/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f34])).
% 8.72/1.48  fof(f34,plain,(
% 8.72/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 8.72/1.48    inference(ennf_transformation,[],[f3])).
% 8.72/1.48  fof(f3,axiom,(
% 8.72/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 8.72/1.48  fof(f111,plain,(
% 8.72/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f5])).
% 8.72/1.48  fof(f5,axiom,(
% 8.72/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 8.72/1.48  fof(f13218,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | (~spl10_1 | ~spl10_73 | spl10_210)),
% 8.72/1.48    inference(subsumption_resolution,[],[f13217,f12228])).
% 8.72/1.48  fof(f12228,plain,(
% 8.72/1.48    ( ! [X0] : (v5_pre_topc(X0,sK3,sK4) | ~v1_xboole_0(X0)) ) | (~spl10_1 | ~spl10_73)),
% 8.72/1.48    inference(superposition,[],[f12227,f114])).
% 8.72/1.48  fof(f12227,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,sK3,sK4) | (~spl10_1 | ~spl10_73)),
% 8.72/1.48    inference(forward_demodulation,[],[f183,f3701])).
% 8.72/1.48  fof(f3701,plain,(
% 8.72/1.48    k1_xboole_0 = sK5 | ~spl10_73),
% 8.72/1.48    inference(avatar_component_clause,[],[f3699])).
% 8.72/1.48  fof(f3699,plain,(
% 8.72/1.48    spl10_73 <=> k1_xboole_0 = sK5),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).
% 8.72/1.48  fof(f183,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,sK4) | ~spl10_1),
% 8.72/1.48    inference(avatar_component_clause,[],[f182])).
% 8.72/1.48  fof(f182,plain,(
% 8.72/1.48    spl10_1 <=> v5_pre_topc(sK5,sK3,sK4)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 8.72/1.48  fof(f13217,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | spl10_210),
% 8.72/1.48    inference(subsumption_resolution,[],[f13216,f97])).
% 8.72/1.48  fof(f97,plain,(
% 8.72/1.48    v2_pre_topc(sK3)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f76,plain,(
% 8.72/1.48    ((((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 8.72/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f71,f75,f74,f73,f72])).
% 8.72/1.48  fof(f72,plain,(
% 8.72/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f73,plain,(
% 8.72/1.48    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(X2,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(X2,sK3,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f74,plain,(
% 8.72/1.48    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(X2,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(X2,sK3,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f75,plain,(
% 8.72/1.48    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(sK6))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f71,plain,(
% 8.72/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.72/1.48    inference(flattening,[],[f70])).
% 8.72/1.48  fof(f70,plain,(
% 8.72/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.72/1.48    inference(nnf_transformation,[],[f31])).
% 8.72/1.48  fof(f31,plain,(
% 8.72/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.72/1.48    inference(flattening,[],[f30])).
% 8.72/1.48  fof(f30,plain,(
% 8.72/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 8.72/1.48    inference(ennf_transformation,[],[f29])).
% 8.72/1.48  fof(f29,negated_conjecture,(
% 8.72/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 8.72/1.48    inference(negated_conjecture,[],[f28])).
% 8.72/1.48  fof(f28,conjecture,(
% 8.72/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 8.72/1.48  fof(f13216,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v2_pre_topc(sK3) | spl10_210),
% 8.72/1.48    inference(subsumption_resolution,[],[f13215,f98])).
% 8.72/1.48  fof(f98,plain,(
% 8.72/1.48    l1_pre_topc(sK3)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f13215,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl10_210),
% 8.72/1.48    inference(subsumption_resolution,[],[f13214,f99])).
% 8.72/1.48  fof(f99,plain,(
% 8.72/1.48    v2_pre_topc(sK4)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f13214,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl10_210),
% 8.72/1.48    inference(subsumption_resolution,[],[f13213,f100])).
% 8.72/1.48  fof(f100,plain,(
% 8.72/1.48    l1_pre_topc(sK4)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f13213,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | ~v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl10_210),
% 8.72/1.48    inference(resolution,[],[f12669,f1364])).
% 8.72/1.48  fof(f1364,plain,(
% 8.72/1.48    ( ! [X17,X16] : (v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17) | ~m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f1363,f153])).
% 8.72/1.48  fof(f153,plain,(
% 8.72/1.48    ( ! [X0,X1] : (v1_funct_1(sK9(X0,X1))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f96])).
% 8.72/1.48  fof(f1363,plain,(
% 8.72/1.48    ( ! [X17,X16] : (~v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17) | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))) | ~m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f1357,f154])).
% 8.72/1.48  fof(f1357,plain,(
% 8.72/1.48    ( ! [X17,X16] : (~v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17) | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))) | ~v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))) | ~m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 8.72/1.48    inference(resolution,[],[f179,f149])).
% 8.72/1.48  fof(f179,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f166])).
% 8.72/1.48  fof(f166,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(equality_resolution,[],[f121])).
% 8.72/1.48  fof(f121,plain,(
% 8.72/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f78])).
% 8.72/1.48  fof(f78,plain,(
% 8.72/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.72/1.48    inference(nnf_transformation,[],[f40])).
% 8.72/1.48  fof(f40,plain,(
% 8.72/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.72/1.48    inference(flattening,[],[f39])).
% 8.72/1.48  fof(f39,plain,(
% 8.72/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.72/1.48    inference(ennf_transformation,[],[f27])).
% 8.72/1.48  fof(f27,axiom,(
% 8.72/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 8.72/1.48  fof(f12669,plain,(
% 8.72/1.48    ( ! [X0] : (~v5_pre_topc(X0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_xboole_0(X0)) ) | spl10_210),
% 8.72/1.48    inference(superposition,[],[f12526,f114])).
% 8.72/1.48  fof(f12526,plain,(
% 8.72/1.48    ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | spl10_210),
% 8.72/1.48    inference(avatar_component_clause,[],[f12525])).
% 8.72/1.48  fof(f12525,plain,(
% 8.72/1.48    spl10_210 <=> v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).
% 8.72/1.48  fof(f12662,plain,(
% 8.72/1.48    ~spl10_206 | spl10_2 | ~spl10_73 | ~spl10_169),
% 8.72/1.48    inference(avatar_split_clause,[],[f12318,f8701,f3699,f186,f12359])).
% 8.72/1.48  fof(f12359,plain,(
% 8.72/1.48    spl10_206 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).
% 8.72/1.48  fof(f186,plain,(
% 8.72/1.48    spl10_2 <=> v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 8.72/1.48  fof(f12318,plain,(
% 8.72/1.48    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (spl10_2 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12317,f3701])).
% 8.72/1.48  fof(f12317,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (spl10_2 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f6557,f8703])).
% 8.72/1.48  fof(f6557,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | spl10_2),
% 8.72/1.48    inference(forward_demodulation,[],[f188,f107])).
% 8.72/1.48  fof(f107,plain,(
% 8.72/1.48    sK5 = sK6),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f188,plain,(
% 8.72/1.48    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | spl10_2),
% 8.72/1.48    inference(avatar_component_clause,[],[f186])).
% 8.72/1.48  fof(f12641,plain,(
% 8.72/1.48    ~spl10_210 | spl10_206 | ~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169),
% 8.72/1.48    inference(avatar_split_clause,[],[f12640,f8701,f3699,f3686,f1324,f1320,f12359,f12525])).
% 8.72/1.48  fof(f1320,plain,(
% 8.72/1.48    spl10_23 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 8.72/1.48  fof(f1324,plain,(
% 8.72/1.48    spl10_24 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 8.72/1.48  fof(f12640,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12639,f540])).
% 8.72/1.48  fof(f12639,plain,(
% 8.72/1.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12638,f3701])).
% 8.72/1.48  fof(f12638,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12637,f8703])).
% 8.72/1.48  fof(f12637,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(sK3),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12636,f3688])).
% 8.72/1.48  fof(f12636,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12635,f111])).
% 8.72/1.48  fof(f12635,plain,(
% 8.72/1.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12634,f3701])).
% 8.72/1.48  fof(f12634,plain,(
% 8.72/1.48    ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12633,f172])).
% 8.72/1.48  fof(f12633,plain,(
% 8.72/1.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12632,f3688])).
% 8.72/1.48  fof(f12632,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12631,f515])).
% 8.72/1.48  fof(f515,plain,(
% 8.72/1.48    v1_funct_1(k1_xboole_0)),
% 8.72/1.48    inference(superposition,[],[f153,f488])).
% 8.72/1.48  fof(f12631,plain,(
% 8.72/1.48    ~v1_funct_1(k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12630,f3701])).
% 8.72/1.48  fof(f12630,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12629,f516])).
% 8.72/1.48  fof(f516,plain,(
% 8.72/1.48    ( ! [X5] : (v1_funct_2(k1_xboole_0,X5,k1_xboole_0)) )),
% 8.72/1.48    inference(superposition,[],[f154,f488])).
% 8.72/1.48  fof(f12629,plain,(
% 8.72/1.48    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12628,f3701])).
% 8.72/1.48  fof(f12628,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12627,f8703])).
% 8.72/1.48  fof(f12627,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12626,f3688])).
% 8.72/1.48  fof(f12626,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12625,f3701])).
% 8.72/1.48  fof(f12625,plain,(
% 8.72/1.48    v5_pre_topc(sK5,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f12079,f8703])).
% 8.72/1.48  fof(f12079,plain,(
% 8.72/1.48    ~v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_73)),
% 8.72/1.48    inference(forward_demodulation,[],[f12078,f3701])).
% 8.72/1.48  fof(f12078,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12077,f97])).
% 8.72/1.48  fof(f12077,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v2_pre_topc(sK3) | (~spl10_23 | ~spl10_24)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12076,f98])).
% 8.72/1.48  fof(f12076,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_23 | ~spl10_24)),
% 8.72/1.48    inference(subsumption_resolution,[],[f12075,f1321])).
% 8.72/1.48  fof(f1321,plain,(
% 8.72/1.48    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_23),
% 8.72/1.48    inference(avatar_component_clause,[],[f1320])).
% 8.72/1.48  fof(f12075,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_24),
% 8.72/1.48    inference(subsumption_resolution,[],[f6369,f1325])).
% 8.72/1.48  fof(f1325,plain,(
% 8.72/1.48    l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_24),
% 8.72/1.48    inference(avatar_component_clause,[],[f1324])).
% 8.72/1.48  fof(f6369,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 8.72/1.48    inference(resolution,[],[f200,f177])).
% 8.72/1.48  fof(f177,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f168])).
% 8.72/1.48  fof(f168,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(equality_resolution,[],[f123])).
% 8.72/1.48  fof(f123,plain,(
% 8.72/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f79])).
% 8.72/1.48  fof(f79,plain,(
% 8.72/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.72/1.48    inference(nnf_transformation,[],[f42])).
% 8.72/1.48  fof(f42,plain,(
% 8.72/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.72/1.48    inference(flattening,[],[f41])).
% 8.72/1.48  fof(f41,plain,(
% 8.72/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.72/1.48    inference(ennf_transformation,[],[f26])).
% 8.72/1.48  fof(f26,axiom,(
% 8.72/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 8.72/1.48  fof(f200,plain,(
% 8.72/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 8.72/1.48    inference(forward_demodulation,[],[f106,f107])).
% 8.72/1.48  fof(f106,plain,(
% 8.72/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f11997,plain,(
% 8.72/1.48    spl10_1 | ~spl10_27 | ~spl10_71 | ~spl10_73 | ~spl10_169),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f11996])).
% 8.72/1.48  fof(f11996,plain,(
% 8.72/1.48    $false | (spl10_1 | ~spl10_27 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11995,f110])).
% 8.72/1.48  fof(f11995,plain,(
% 8.72/1.48    ~v1_xboole_0(k1_xboole_0) | (spl10_1 | ~spl10_27 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f11994,f488])).
% 8.72/1.48  fof(f11994,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),k1_xboole_0)) | (spl10_1 | ~spl10_27 | ~spl10_71 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f11993,f3688])).
% 8.72/1.48  fof(f11993,plain,(
% 8.72/1.48    ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (spl10_1 | ~spl10_27 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11992,f540])).
% 8.72/1.48  fof(f11992,plain,(
% 8.72/1.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (spl10_1 | ~spl10_27 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f11991,f501])).
% 8.72/1.48  fof(f11991,plain,(
% 8.72/1.48    ~v1_funct_2(sK9(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_xboole_0,u1_struct_0(sK4)) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (spl10_1 | ~spl10_27 | ~spl10_73 | ~spl10_169)),
% 8.72/1.48    inference(forward_demodulation,[],[f11990,f8703])).
% 8.72/1.48  fof(f11990,plain,(
% 8.72/1.48    ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (spl10_1 | ~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11989,f193])).
% 8.72/1.48  fof(f11989,plain,(
% 8.72/1.48    ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (spl10_1 | ~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11988,f8347])).
% 8.72/1.48  fof(f8347,plain,(
% 8.72/1.48    ( ! [X0] : (~v5_pre_topc(X0,sK3,sK4) | ~v1_xboole_0(X0)) ) | (spl10_1 | ~spl10_73)),
% 8.72/1.48    inference(superposition,[],[f3730,f114])).
% 8.72/1.48  fof(f3730,plain,(
% 8.72/1.48    ~v5_pre_topc(k1_xboole_0,sK3,sK4) | (spl10_1 | ~spl10_73)),
% 8.72/1.48    inference(backward_demodulation,[],[f184,f3701])).
% 8.72/1.48  fof(f184,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | spl10_1),
% 8.72/1.48    inference(avatar_component_clause,[],[f182])).
% 8.72/1.48  fof(f11988,plain,(
% 8.72/1.48    v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11987,f97])).
% 8.72/1.48  fof(f11987,plain,(
% 8.72/1.48    v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v2_pre_topc(sK3) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11986,f98])).
% 8.72/1.48  fof(f11986,plain,(
% 8.72/1.48    v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11985,f99])).
% 8.72/1.48  fof(f11985,plain,(
% 8.72/1.48    v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f11960,f100])).
% 8.72/1.48  fof(f11960,plain,(
% 8.72/1.48    v5_pre_topc(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),sK3,sK4) | ~m1_subset_1(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~v1_xboole_0(sK9(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(resolution,[],[f1477,f9255])).
% 8.72/1.48  fof(f9255,plain,(
% 8.72/1.48    ( ! [X0] : (v5_pre_topc(X0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_xboole_0(X0)) ) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(superposition,[],[f9247,f114])).
% 8.72/1.48  fof(f9247,plain,(
% 8.72/1.48    v5_pre_topc(k1_xboole_0,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl10_27 | ~spl10_73)),
% 8.72/1.48    inference(forward_demodulation,[],[f1338,f3701])).
% 8.72/1.48  fof(f1338,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_27),
% 8.72/1.48    inference(avatar_component_clause,[],[f1336])).
% 8.72/1.48  fof(f1336,plain,(
% 8.72/1.48    spl10_27 <=> v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 8.72/1.48  fof(f1477,plain,(
% 8.72/1.48    ( ! [X17,X16] : (~v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17) | ~m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f1476,f153])).
% 8.72/1.48  fof(f1476,plain,(
% 8.72/1.48    ( ! [X17,X16] : (~v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17) | ~v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))) | ~m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f1442,f154])).
% 8.72/1.48  fof(f1442,plain,(
% 8.72/1.48    ( ! [X17,X16] : (~v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | v5_pre_topc(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),X16,X17) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))) | ~v1_funct_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))) | ~m1_subset_1(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17)))) | ~v1_funct_2(sK9(u1_struct_0(X16),u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))),u1_struct_0(X16),u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) )),
% 8.72/1.48    inference(resolution,[],[f180,f149])).
% 8.72/1.48  fof(f180,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f165])).
% 8.72/1.48  fof(f165,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(equality_resolution,[],[f122])).
% 8.72/1.48  fof(f122,plain,(
% 8.72/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f78])).
% 8.72/1.48  fof(f9246,plain,(
% 8.72/1.48    spl10_26 | ~spl10_71 | ~spl10_73),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f9245])).
% 8.72/1.48  fof(f9245,plain,(
% 8.72/1.48    $false | (spl10_26 | ~spl10_71 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f9244,f111])).
% 8.72/1.48  fof(f9244,plain,(
% 8.72/1.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl10_26 | ~spl10_71 | ~spl10_73)),
% 8.72/1.48    inference(forward_demodulation,[],[f9243,f3701])).
% 8.72/1.48  fof(f9243,plain,(
% 8.72/1.48    ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | (spl10_26 | ~spl10_71)),
% 8.72/1.48    inference(forward_demodulation,[],[f9242,f172])).
% 8.72/1.48  fof(f9242,plain,(
% 8.72/1.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) | (spl10_26 | ~spl10_71)),
% 8.72/1.48    inference(forward_demodulation,[],[f1334,f3688])).
% 8.72/1.48  fof(f1334,plain,(
% 8.72/1.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | spl10_26),
% 8.72/1.48    inference(avatar_component_clause,[],[f1332])).
% 8.72/1.48  fof(f1332,plain,(
% 8.72/1.48    spl10_26 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 8.72/1.48  fof(f8705,plain,(
% 8.72/1.48    spl10_169 | ~spl10_15 | ~spl10_76),
% 8.72/1.48    inference(avatar_split_clause,[],[f8693,f3840,f454,f8701])).
% 8.72/1.48  fof(f454,plain,(
% 8.72/1.48    spl10_15 <=> ! [X7] : ~r2_hidden(X7,k1_xboole_0)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 8.72/1.48  fof(f3840,plain,(
% 8.72/1.48    spl10_76 <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK3))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).
% 8.72/1.48  fof(f8693,plain,(
% 8.72/1.48    k1_xboole_0 = u1_struct_0(sK3) | (~spl10_15 | ~spl10_76)),
% 8.72/1.48    inference(resolution,[],[f8632,f587])).
% 8.72/1.48  fof(f587,plain,(
% 8.72/1.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl10_15),
% 8.72/1.48    inference(resolution,[],[f481,f127])).
% 8.72/1.48  fof(f481,plain,(
% 8.72/1.48    ( ! [X2,X1] : (~r2_hidden(X1,X2) | ~r1_tarski(X2,k1_xboole_0)) ) | ~spl10_15),
% 8.72/1.48    inference(resolution,[],[f455,f141])).
% 8.72/1.48  fof(f141,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f91])).
% 8.72/1.48  fof(f91,plain,(
% 8.72/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.72/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f89,f90])).
% 8.72/1.48  fof(f90,plain,(
% 8.72/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 8.72/1.48    introduced(choice_axiom,[])).
% 8.72/1.48  fof(f89,plain,(
% 8.72/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.72/1.48    inference(rectify,[],[f88])).
% 8.72/1.48  fof(f88,plain,(
% 8.72/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.72/1.48    inference(nnf_transformation,[],[f52])).
% 8.72/1.48  fof(f52,plain,(
% 8.72/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.72/1.48    inference(ennf_transformation,[],[f1])).
% 8.72/1.48  fof(f1,axiom,(
% 8.72/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 8.72/1.48  fof(f455,plain,(
% 8.72/1.48    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) ) | ~spl10_15),
% 8.72/1.48    inference(avatar_component_clause,[],[f454])).
% 8.72/1.48  fof(f8632,plain,(
% 8.72/1.48    ( ! [X0] : (r1_tarski(u1_struct_0(sK3),X0)) ) | ~spl10_76),
% 8.72/1.48    inference(resolution,[],[f3842,f2345])).
% 8.72/1.48  fof(f2345,plain,(
% 8.72/1.48    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | r1_tarski(X0,X1)) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f2344,f291])).
% 8.72/1.48  fof(f291,plain,(
% 8.72/1.48    v1_relat_1(k1_xboole_0)),
% 8.72/1.48    inference(resolution,[],[f155,f111])).
% 8.72/1.48  fof(f155,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f53])).
% 8.72/1.48  fof(f53,plain,(
% 8.72/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.72/1.48    inference(ennf_transformation,[],[f11])).
% 8.72/1.48  fof(f11,axiom,(
% 8.72/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 8.72/1.48  fof(f2344,plain,(
% 8.72/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_partfun1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 8.72/1.48    inference(subsumption_resolution,[],[f2336,f400])).
% 8.72/1.48  fof(f400,plain,(
% 8.72/1.48    ( ! [X5] : (v4_relat_1(k1_xboole_0,X5)) )),
% 8.72/1.48    inference(resolution,[],[f158,f111])).
% 8.72/1.48  fof(f158,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f56])).
% 8.72/1.48  fof(f56,plain,(
% 8.72/1.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.72/1.48    inference(ennf_transformation,[],[f12])).
% 8.72/1.48  fof(f12,axiom,(
% 8.72/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 8.72/1.48  fof(f2336,plain,(
% 8.72/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_partfun1(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 8.72/1.48    inference(superposition,[],[f2232,f139])).
% 8.72/1.48  fof(f139,plain,(
% 8.72/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f87])).
% 8.72/1.48  fof(f87,plain,(
% 8.72/1.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.72/1.48    inference(nnf_transformation,[],[f51])).
% 8.72/1.48  fof(f51,plain,(
% 8.72/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.72/1.48    inference(flattening,[],[f50])).
% 8.72/1.48  fof(f50,plain,(
% 8.72/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 8.72/1.48    inference(ennf_transformation,[],[f19])).
% 8.72/1.48  fof(f19,axiom,(
% 8.72/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 8.72/1.48  fof(f2232,plain,(
% 8.72/1.48    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 8.72/1.48    inference(resolution,[],[f2183,f144])).
% 8.72/1.48  fof(f144,plain,(
% 8.72/1.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f92])).
% 8.72/1.48  fof(f92,plain,(
% 8.72/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.72/1.48    inference(nnf_transformation,[],[f6])).
% 8.72/1.48  fof(f6,axiom,(
% 8.72/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 8.72/1.48  fof(f2183,plain,(
% 8.72/1.48    ( ! [X10] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X10))) )),
% 8.72/1.48    inference(resolution,[],[f904,f111])).
% 8.72/1.48  fof(f904,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f903])).
% 8.72/1.48  fof(f903,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.72/1.48    inference(superposition,[],[f157,f156])).
% 8.72/1.48  fof(f156,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f54])).
% 8.72/1.48  fof(f54,plain,(
% 8.72/1.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.72/1.48    inference(ennf_transformation,[],[f14])).
% 8.72/1.48  fof(f14,axiom,(
% 8.72/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 8.72/1.48  fof(f157,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f55])).
% 8.72/1.48  fof(f55,plain,(
% 8.72/1.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.72/1.48    inference(ennf_transformation,[],[f13])).
% 8.72/1.48  fof(f13,axiom,(
% 8.72/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 8.72/1.48  fof(f3842,plain,(
% 8.72/1.48    v1_partfun1(k1_xboole_0,u1_struct_0(sK3)) | ~spl10_76),
% 8.72/1.48    inference(avatar_component_clause,[],[f3840])).
% 8.72/1.48  fof(f8454,plain,(
% 8.72/1.48    spl10_76 | ~spl10_73 | ~spl10_79),
% 8.72/1.48    inference(avatar_split_clause,[],[f8410,f3894,f3699,f3840])).
% 8.72/1.48  fof(f3894,plain,(
% 8.72/1.48    spl10_79 <=> v1_partfun1(sK5,u1_struct_0(sK3))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).
% 8.72/1.48  fof(f8410,plain,(
% 8.72/1.48    v1_partfun1(k1_xboole_0,u1_struct_0(sK3)) | (~spl10_73 | ~spl10_79)),
% 8.72/1.48    inference(backward_demodulation,[],[f3896,f3701])).
% 8.72/1.48  fof(f3896,plain,(
% 8.72/1.48    v1_partfun1(sK5,u1_struct_0(sK3)) | ~spl10_79),
% 8.72/1.48    inference(avatar_component_clause,[],[f3894])).
% 8.72/1.48  fof(f8190,plain,(
% 8.72/1.48    spl10_73 | ~spl10_18),
% 8.72/1.48    inference(avatar_split_clause,[],[f868,f464,f3699])).
% 8.72/1.48  fof(f464,plain,(
% 8.72/1.48    spl10_18 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 8.72/1.48  fof(f868,plain,(
% 8.72/1.48    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) | k1_xboole_0 = sK5),
% 8.72/1.48    inference(resolution,[],[f857,f201])).
% 8.72/1.48  fof(f201,plain,(
% 8.72/1.48    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))),
% 8.72/1.48    inference(resolution,[],[f144,f103])).
% 8.72/1.48  fof(f103,plain,(
% 8.72/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f857,plain,(
% 8.72/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_xboole_0(X0) | k1_xboole_0 = X1) )),
% 8.72/1.48    inference(resolution,[],[f439,f127])).
% 8.72/1.48  fof(f439,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~v1_xboole_0(X0) | ~r1_tarski(X2,X0)) )),
% 8.72/1.48    inference(resolution,[],[f163,f145])).
% 8.72/1.48  fof(f145,plain,(
% 8.72/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f92])).
% 8.72/1.48  fof(f8164,plain,(
% 8.72/1.48    spl10_73 | ~spl10_34),
% 8.72/1.48    inference(avatar_split_clause,[],[f4019,f2014,f3699])).
% 8.72/1.48  fof(f2014,plain,(
% 8.72/1.48    spl10_34 <=> r1_tarski(sK5,k1_xboole_0)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 8.72/1.48  fof(f4019,plain,(
% 8.72/1.48    k1_xboole_0 = sK5 | ~spl10_34),
% 8.72/1.48    inference(subsumption_resolution,[],[f4014,f110])).
% 8.72/1.48  fof(f4014,plain,(
% 8.72/1.48    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK5 | ~spl10_34),
% 8.72/1.48    inference(resolution,[],[f2015,f857])).
% 8.72/1.48  fof(f2015,plain,(
% 8.72/1.48    r1_tarski(sK5,k1_xboole_0) | ~spl10_34),
% 8.72/1.48    inference(avatar_component_clause,[],[f2014])).
% 8.72/1.48  fof(f8147,plain,(
% 8.72/1.48    spl10_34 | ~spl10_71),
% 8.72/1.48    inference(avatar_split_clause,[],[f7338,f3686,f2014])).
% 8.72/1.48  fof(f7338,plain,(
% 8.72/1.48    r1_tarski(sK5,k1_xboole_0) | ~spl10_71),
% 8.72/1.48    inference(forward_demodulation,[],[f7305,f172])).
% 8.72/1.48  fof(f7305,plain,(
% 8.72/1.48    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)) | ~spl10_71),
% 8.72/1.48    inference(backward_demodulation,[],[f202,f3688])).
% 8.72/1.48  fof(f202,plain,(
% 8.72/1.48    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))),
% 8.72/1.48    inference(resolution,[],[f144,f200])).
% 8.72/1.48  fof(f8130,plain,(
% 8.72/1.48    spl10_6 | spl10_69 | ~spl10_80),
% 8.72/1.48    inference(avatar_split_clause,[],[f8129,f3899,f3669,f228])).
% 8.72/1.48  fof(f228,plain,(
% 8.72/1.48    spl10_6 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 8.72/1.48  fof(f3669,plain,(
% 8.72/1.48    spl10_69 <=> v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).
% 8.72/1.48  fof(f3899,plain,(
% 8.72/1.48    spl10_80 <=> v1_funct_1(sK5)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).
% 8.72/1.48  fof(f8129,plain,(
% 8.72/1.48    v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~spl10_80),
% 8.72/1.48    inference(subsumption_resolution,[],[f8128,f198])).
% 8.72/1.48  fof(f198,plain,(
% 8.72/1.48    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 8.72/1.48    inference(forward_demodulation,[],[f105,f107])).
% 8.72/1.48  fof(f105,plain,(
% 8.72/1.48    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f8128,plain,(
% 8.72/1.48    v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~spl10_80),
% 8.72/1.48    inference(subsumption_resolution,[],[f5511,f3900])).
% 8.72/1.48  fof(f3900,plain,(
% 8.72/1.48    v1_funct_1(sK5) | ~spl10_80),
% 8.72/1.48    inference(avatar_component_clause,[],[f3899])).
% 8.72/1.48  fof(f5511,plain,(
% 8.72/1.48    ~v1_funct_1(sK5) | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 8.72/1.48    inference(resolution,[],[f1051,f202])).
% 8.72/1.48  fof(f1051,plain,(
% 8.72/1.48    ( ! [X6,X7,X5] : (~r1_tarski(X5,k2_zfmisc_1(X6,X7)) | ~v1_funct_1(X5) | v1_partfun1(X5,X6) | v1_xboole_0(X7) | ~v1_funct_2(X5,X6,X7)) )),
% 8.72/1.48    inference(resolution,[],[f130,f145])).
% 8.72/1.48  fof(f130,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f45])).
% 8.72/1.48  fof(f45,plain,(
% 8.72/1.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.72/1.48    inference(flattening,[],[f44])).
% 8.72/1.48  fof(f44,plain,(
% 8.72/1.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.72/1.48    inference(ennf_transformation,[],[f17])).
% 8.72/1.48  fof(f17,axiom,(
% 8.72/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 8.72/1.48  fof(f8124,plain,(
% 8.72/1.48    spl10_69 | spl10_71 | ~spl10_80),
% 8.72/1.48    inference(avatar_split_clause,[],[f8123,f3899,f3686,f3669])).
% 8.72/1.48  fof(f8123,plain,(
% 8.72/1.48    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~spl10_80),
% 8.72/1.48    inference(subsumption_resolution,[],[f8122,f3900])).
% 8.72/1.48  fof(f8122,plain,(
% 8.72/1.48    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~v1_funct_1(sK5)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6377,f198])).
% 8.72/1.48  fof(f6377,plain,(
% 8.72/1.48    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5)),
% 8.72/1.48    inference(resolution,[],[f200,f175])).
% 8.72/1.48  fof(f175,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f160])).
% 8.72/1.48  fof(f160,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f58])).
% 8.72/1.48  fof(f58,plain,(
% 8.72/1.48    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 8.72/1.48    inference(flattening,[],[f57])).
% 8.72/1.48  fof(f57,plain,(
% 8.72/1.48    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 8.72/1.48    inference(ennf_transformation,[],[f21])).
% 8.72/1.48  fof(f21,axiom,(
% 8.72/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 8.72/1.48  fof(f8103,plain,(
% 8.72/1.48    ~spl10_69 | spl10_30 | ~spl10_79 | ~spl10_81 | ~spl10_109),
% 8.72/1.48    inference(avatar_split_clause,[],[f8102,f6732,f3903,f3894,f1464,f3669])).
% 8.72/1.48  fof(f1464,plain,(
% 8.72/1.48    spl10_30 <=> v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 8.72/1.48  fof(f3903,plain,(
% 8.72/1.48    spl10_81 <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).
% 8.72/1.48  fof(f6732,plain,(
% 8.72/1.48    spl10_109 <=> v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).
% 8.72/1.48  fof(f8102,plain,(
% 8.72/1.48    ~v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | (spl10_30 | ~spl10_79 | ~spl10_81 | ~spl10_109)),
% 8.72/1.48    inference(subsumption_resolution,[],[f7876,f6733])).
% 8.72/1.48  fof(f6733,plain,(
% 8.72/1.48    v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~spl10_109),
% 8.72/1.48    inference(avatar_component_clause,[],[f6732])).
% 8.72/1.48  fof(f7876,plain,(
% 8.72/1.48    ~v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | (spl10_30 | ~spl10_79 | ~spl10_81)),
% 8.72/1.48    inference(resolution,[],[f7639,f1466])).
% 8.72/1.48  fof(f1466,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | spl10_30),
% 8.72/1.48    inference(avatar_component_clause,[],[f1464])).
% 8.72/1.48  fof(f7639,plain,(
% 8.72/1.48    ( ! [X37] : (v1_funct_2(sK5,X37,u1_struct_0(sK4)) | ~v1_partfun1(sK5,X37) | ~v4_relat_1(sK5,X37)) ) | (~spl10_79 | ~spl10_81)),
% 8.72/1.48    inference(superposition,[],[f3904,f5730])).
% 8.72/1.48  fof(f5730,plain,(
% 8.72/1.48    ( ! [X18] : (u1_struct_0(sK3) = X18 | ~v1_partfun1(sK5,X18) | ~v4_relat_1(sK5,X18)) ) | ~spl10_79),
% 8.72/1.48    inference(subsumption_resolution,[],[f5729,f292])).
% 8.72/1.48  fof(f292,plain,(
% 8.72/1.48    v1_relat_1(sK5)),
% 8.72/1.48    inference(resolution,[],[f155,f103])).
% 8.72/1.48  fof(f5729,plain,(
% 8.72/1.48    ( ! [X18] : (u1_struct_0(sK3) = X18 | ~v1_relat_1(sK5) | ~v1_partfun1(sK5,X18) | ~v4_relat_1(sK5,X18)) ) | ~spl10_79),
% 8.72/1.48    inference(subsumption_resolution,[],[f5709,f401])).
% 8.72/1.48  fof(f401,plain,(
% 8.72/1.48    v4_relat_1(sK5,u1_struct_0(sK3))),
% 8.72/1.48    inference(resolution,[],[f158,f103])).
% 8.72/1.48  fof(f5709,plain,(
% 8.72/1.48    ( ! [X18] : (u1_struct_0(sK3) = X18 | ~v4_relat_1(sK5,u1_struct_0(sK3)) | ~v1_relat_1(sK5) | ~v1_partfun1(sK5,X18) | ~v4_relat_1(sK5,X18)) ) | ~spl10_79),
% 8.72/1.48    inference(resolution,[],[f814,f3896])).
% 8.72/1.48  fof(f814,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X2) | X1 = X2 | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f808])).
% 8.72/1.48  fof(f808,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (X1 = X2 | ~v1_partfun1(X0,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 8.72/1.48    inference(superposition,[],[f139,f139])).
% 8.72/1.48  fof(f3904,plain,(
% 8.72/1.48    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~spl10_81),
% 8.72/1.48    inference(avatar_component_clause,[],[f3903])).
% 8.72/1.48  fof(f8052,plain,(
% 8.72/1.48    ~spl10_25 | ~spl10_26 | spl10_27 | ~spl10_23 | ~spl10_24 | ~spl10_80 | ~spl10_104),
% 8.72/1.48    inference(avatar_split_clause,[],[f8051,f6513,f3899,f1324,f1320,f1336,f1332,f1328])).
% 8.72/1.48  fof(f1328,plain,(
% 8.72/1.48    spl10_25 <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 8.72/1.48  fof(f6513,plain,(
% 8.72/1.48    spl10_104 <=> v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).
% 8.72/1.48  fof(f8051,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (~spl10_23 | ~spl10_24 | ~spl10_80 | ~spl10_104)),
% 8.72/1.48    inference(subsumption_resolution,[],[f8050,f97])).
% 8.72/1.48  fof(f8050,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v2_pre_topc(sK3) | (~spl10_23 | ~spl10_24 | ~spl10_80 | ~spl10_104)),
% 8.72/1.48    inference(subsumption_resolution,[],[f8049,f98])).
% 8.72/1.48  fof(f8049,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_23 | ~spl10_24 | ~spl10_80 | ~spl10_104)),
% 8.72/1.48    inference(subsumption_resolution,[],[f8048,f1321])).
% 8.72/1.48  fof(f8048,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_24 | ~spl10_80 | ~spl10_104)),
% 8.72/1.48    inference(subsumption_resolution,[],[f8047,f1325])).
% 8.72/1.48  fof(f8047,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_80 | ~spl10_104)),
% 8.72/1.48    inference(subsumption_resolution,[],[f8046,f3900])).
% 8.72/1.48  fof(f8046,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_104),
% 8.72/1.48    inference(subsumption_resolution,[],[f8045,f198])).
% 8.72/1.48  fof(f8045,plain,(
% 8.72/1.48    v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_104),
% 8.72/1.48    inference(subsumption_resolution,[],[f6368,f6515])).
% 8.72/1.48  fof(f6515,plain,(
% 8.72/1.48    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_104),
% 8.72/1.48    inference(avatar_component_clause,[],[f6513])).
% 8.72/1.48  fof(f6368,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 8.72/1.48    inference(resolution,[],[f200,f178])).
% 8.72/1.48  fof(f178,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f167])).
% 8.72/1.48  fof(f167,plain,(
% 8.72/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(equality_resolution,[],[f124])).
% 8.72/1.48  fof(f124,plain,(
% 8.72/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f79])).
% 8.72/1.48  fof(f6840,plain,(
% 8.72/1.48    spl10_109),
% 8.72/1.48    inference(avatar_split_clause,[],[f6375,f6732])).
% 8.72/1.48  fof(f6375,plain,(
% 8.72/1.48    v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 8.72/1.48    inference(resolution,[],[f200,f158])).
% 8.72/1.48  fof(f6715,plain,(
% 8.72/1.48    ~spl10_30 | spl10_104 | ~spl10_32 | ~spl10_28 | ~spl10_29 | ~spl10_31 | ~spl10_80),
% 8.72/1.48    inference(avatar_split_clause,[],[f6714,f3899,f1468,f1460,f1456,f1472,f6513,f1464])).
% 8.72/1.48  fof(f1472,plain,(
% 8.72/1.48    spl10_32 <=> v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 8.72/1.48  fof(f1456,plain,(
% 8.72/1.48    spl10_28 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 8.72/1.48  fof(f1460,plain,(
% 8.72/1.48    spl10_29 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 8.72/1.48  fof(f1468,plain,(
% 8.72/1.48    spl10_31 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 8.72/1.48  fof(f6714,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | (~spl10_28 | ~spl10_29 | ~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6713,f1457])).
% 8.72/1.48  fof(f1457,plain,(
% 8.72/1.48    v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~spl10_28),
% 8.72/1.48    inference(avatar_component_clause,[],[f1456])).
% 8.72/1.48  fof(f6713,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_29 | ~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6712,f1461])).
% 8.72/1.48  fof(f1461,plain,(
% 8.72/1.48    l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~spl10_29),
% 8.72/1.48    inference(avatar_component_clause,[],[f1460])).
% 8.72/1.48  fof(f6712,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6711,f99])).
% 8.72/1.48  fof(f6711,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6710,f100])).
% 8.72/1.48  fof(f6710,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6506,f1469])).
% 8.72/1.48  fof(f1469,plain,(
% 8.72/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~spl10_31),
% 8.72/1.48    inference(avatar_component_clause,[],[f1468])).
% 8.72/1.48  fof(f6506,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~spl10_80),
% 8.72/1.48    inference(subsumption_resolution,[],[f6505,f3900])).
% 8.72/1.48  fof(f6505,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 8.72/1.48    inference(subsumption_resolution,[],[f6371,f198])).
% 8.72/1.48  fof(f6371,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 8.72/1.48    inference(resolution,[],[f200,f179])).
% 8.72/1.48  fof(f6709,plain,(
% 8.72/1.48    ~spl10_30 | spl10_32 | ~spl10_104 | ~spl10_28 | ~spl10_29 | ~spl10_31 | ~spl10_80),
% 8.72/1.48    inference(avatar_split_clause,[],[f6708,f3899,f1468,f1460,f1456,f6513,f1472,f1464])).
% 8.72/1.48  fof(f6708,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | (~spl10_28 | ~spl10_29 | ~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6707,f1457])).
% 8.72/1.48  fof(f6707,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_29 | ~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6706,f1461])).
% 8.72/1.48  fof(f6706,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6705,f99])).
% 8.72/1.48  fof(f6705,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6704,f100])).
% 8.72/1.48  fof(f6704,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6518,f1469])).
% 8.72/1.48  fof(f6518,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~spl10_80),
% 8.72/1.48    inference(subsumption_resolution,[],[f6517,f3900])).
% 8.72/1.48  fof(f6517,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 8.72/1.48    inference(subsumption_resolution,[],[f6370,f198])).
% 8.72/1.48  fof(f6370,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 8.72/1.48    inference(resolution,[],[f200,f180])).
% 8.72/1.48  fof(f6671,plain,(
% 8.72/1.48    ~spl10_30 | spl10_32 | ~spl10_1 | ~spl10_31 | ~spl10_80 | ~spl10_81),
% 8.72/1.48    inference(avatar_split_clause,[],[f6670,f3903,f3899,f1468,f182,f1472,f1464])).
% 8.72/1.48  fof(f6670,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6669,f97])).
% 8.72/1.48  fof(f6669,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6668,f98])).
% 8.72/1.48  fof(f6668,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6667,f99])).
% 8.72/1.48  fof(f6667,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6666,f100])).
% 8.72/1.48  fof(f6666,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6665,f3904])).
% 8.72/1.48  fof(f6665,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6664,f103])).
% 8.72/1.48  fof(f6664,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6591,f3900])).
% 8.72/1.48  fof(f6591,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_31),
% 8.72/1.48    inference(resolution,[],[f1469,f177])).
% 8.72/1.48  fof(f6663,plain,(
% 8.72/1.48    ~spl10_30 | spl10_1 | ~spl10_32 | ~spl10_31 | ~spl10_80 | ~spl10_81),
% 8.72/1.48    inference(avatar_split_clause,[],[f6662,f3903,f3899,f1468,f1472,f182,f1464])).
% 8.72/1.48  fof(f6662,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6661,f97])).
% 8.72/1.48  fof(f6661,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6660,f98])).
% 8.72/1.48  fof(f6660,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6659,f99])).
% 8.72/1.48  fof(f6659,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6658,f100])).
% 8.72/1.48  fof(f6658,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80 | ~spl10_81)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6657,f3904])).
% 8.72/1.48  fof(f6657,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6656,f103])).
% 8.72/1.48  fof(f6656,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_31 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f6590,f3900])).
% 8.72/1.48  fof(f6590,plain,(
% 8.72/1.48    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_31),
% 8.72/1.48    inference(resolution,[],[f1469,f178])).
% 8.72/1.48  fof(f6655,plain,(
% 8.72/1.48    spl10_104 | ~spl10_2),
% 8.72/1.48    inference(avatar_split_clause,[],[f6654,f186,f6513])).
% 8.72/1.48  fof(f6654,plain,(
% 8.72/1.48    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_2),
% 8.72/1.48    inference(forward_demodulation,[],[f187,f107])).
% 8.72/1.48  fof(f187,plain,(
% 8.72/1.48    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl10_2),
% 8.72/1.48    inference(avatar_component_clause,[],[f186])).
% 8.72/1.48  fof(f6558,plain,(
% 8.72/1.48    ~spl10_104 | spl10_2),
% 8.72/1.48    inference(avatar_split_clause,[],[f6557,f186,f6513])).
% 8.72/1.48  fof(f6503,plain,(
% 8.72/1.48    spl10_31),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f6494])).
% 8.72/1.48  fof(f6494,plain,(
% 8.72/1.48    $false | spl10_31),
% 8.72/1.48    inference(subsumption_resolution,[],[f103,f6468])).
% 8.72/1.48  fof(f6468,plain,(
% 8.72/1.48    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK4))))) ) | spl10_31),
% 8.72/1.48    inference(subsumption_resolution,[],[f6460,f2208])).
% 8.72/1.48  fof(f2208,plain,(
% 8.72/1.48    r1_tarski(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 8.72/1.48    inference(resolution,[],[f2186,f144])).
% 8.72/1.48  fof(f2186,plain,(
% 8.72/1.48    m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))),
% 8.72/1.48    inference(resolution,[],[f904,f200])).
% 8.72/1.48  fof(f6460,plain,(
% 8.72/1.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK4))))) ) | spl10_31),
% 8.72/1.48    inference(resolution,[],[f1470,f164])).
% 8.72/1.48  fof(f164,plain,(
% 8.72/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f63])).
% 8.72/1.48  fof(f63,plain,(
% 8.72/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 8.72/1.48    inference(flattening,[],[f62])).
% 8.72/1.48  fof(f62,plain,(
% 8.72/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 8.72/1.48    inference(ennf_transformation,[],[f15])).
% 8.72/1.48  fof(f15,axiom,(
% 8.72/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 8.72/1.48  fof(f1470,plain,(
% 8.72/1.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | spl10_31),
% 8.72/1.48    inference(avatar_component_clause,[],[f1468])).
% 8.72/1.48  fof(f3965,plain,(
% 8.72/1.48    spl10_79 | ~spl10_81 | spl10_3 | ~spl10_80),
% 8.72/1.48    inference(avatar_split_clause,[],[f3964,f3899,f214,f3903,f3894])).
% 8.72/1.48  fof(f214,plain,(
% 8.72/1.48    spl10_3 <=> v1_xboole_0(u1_struct_0(sK4))),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 8.72/1.48  fof(f3964,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v1_partfun1(sK5,u1_struct_0(sK3)) | (spl10_3 | ~spl10_80)),
% 8.72/1.48    inference(subsumption_resolution,[],[f3963,f216])).
% 8.72/1.48  fof(f216,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(sK4)) | spl10_3),
% 8.72/1.48    inference(avatar_component_clause,[],[f214])).
% 8.72/1.48  fof(f3963,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v1_partfun1(sK5,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK4)) | ~spl10_80),
% 8.72/1.48    inference(subsumption_resolution,[],[f3943,f3900])).
% 8.72/1.48  fof(f3943,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~v1_funct_1(sK5) | v1_partfun1(sK5,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK4))),
% 8.72/1.48    inference(resolution,[],[f103,f130])).
% 8.72/1.48  fof(f3931,plain,(
% 8.72/1.48    spl10_80),
% 8.72/1.48    inference(avatar_split_clause,[],[f101,f3899])).
% 8.72/1.48  fof(f101,plain,(
% 8.72/1.48    v1_funct_1(sK5)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f3930,plain,(
% 8.72/1.48    spl10_81),
% 8.72/1.48    inference(avatar_split_clause,[],[f102,f3903])).
% 8.72/1.48  fof(f102,plain,(
% 8.72/1.48    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f3845,plain,(
% 8.72/1.48    ~spl10_3 | spl10_18),
% 8.72/1.48    inference(avatar_split_clause,[],[f477,f464,f214])).
% 8.72/1.48  fof(f477,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(sK4)) | spl10_18),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f476])).
% 8.72/1.48  fof(f476,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(sK4)) | ~v1_xboole_0(u1_struct_0(sK4)) | spl10_18),
% 8.72/1.48    inference(superposition,[],[f466,f195])).
% 8.72/1.48  fof(f195,plain,(
% 8.72/1.48    ( ! [X0,X1] : (k2_zfmisc_1(X1,X0) = X0 | ~v1_xboole_0(X0)) )),
% 8.72/1.48    inference(superposition,[],[f172,f114])).
% 8.72/1.48  fof(f466,plain,(
% 8.72/1.48    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) | spl10_18),
% 8.72/1.48    inference(avatar_component_clause,[],[f464])).
% 8.72/1.48  fof(f3828,plain,(
% 8.72/1.48    ~spl10_3 | spl10_30 | ~spl10_73),
% 8.72/1.48    inference(avatar_split_clause,[],[f3827,f3699,f1464,f214])).
% 8.72/1.48  fof(f3827,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(sK4)) | (spl10_30 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f3826,f110])).
% 8.72/1.48  fof(f3826,plain,(
% 8.72/1.48    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(u1_struct_0(sK4)) | (spl10_30 | ~spl10_73)),
% 8.72/1.48    inference(forward_demodulation,[],[f1863,f3701])).
% 8.72/1.48  fof(f1863,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(sK4)) | ~v1_xboole_0(sK5) | spl10_30),
% 8.72/1.48    inference(resolution,[],[f701,f1466])).
% 8.72/1.48  fof(f701,plain,(
% 8.72/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 8.72/1.48    inference(superposition,[],[f675,f114])).
% 8.72/1.48  fof(f675,plain,(
% 8.72/1.48    ( ! [X10,X11] : (v1_funct_2(k1_xboole_0,X10,X11) | ~v1_xboole_0(X11)) )),
% 8.72/1.48    inference(superposition,[],[f154,f594])).
% 8.72/1.48  fof(f594,plain,(
% 8.72/1.48    ( ! [X0,X1] : (k1_xboole_0 = sK9(X1,X0) | ~v1_xboole_0(X0)) )),
% 8.72/1.48    inference(resolution,[],[f450,f127])).
% 8.72/1.48  fof(f450,plain,(
% 8.72/1.48    ( ! [X17,X15,X16] : (~r2_hidden(X16,sK9(X17,X15)) | ~v1_xboole_0(X15)) )),
% 8.72/1.48    inference(duplicate_literal_removal,[],[f446])).
% 8.72/1.48  fof(f446,plain,(
% 8.72/1.48    ( ! [X17,X15,X16] : (~v1_xboole_0(X15) | ~r2_hidden(X16,sK9(X17,X15)) | ~v1_xboole_0(X15)) )),
% 8.72/1.48    inference(resolution,[],[f163,f282])).
% 8.72/1.48  fof(f282,plain,(
% 8.72/1.48    ( ! [X4,X3] : (m1_subset_1(sK9(X3,X4),k1_zfmisc_1(X4)) | ~v1_xboole_0(X4)) )),
% 8.72/1.48    inference(superposition,[],[f149,f195])).
% 8.72/1.48  fof(f3807,plain,(
% 8.72/1.48    ~spl10_6 | spl10_25 | ~spl10_73),
% 8.72/1.48    inference(avatar_split_clause,[],[f3806,f3699,f1328,f228])).
% 8.72/1.48  fof(f3806,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (spl10_25 | ~spl10_73)),
% 8.72/1.48    inference(subsumption_resolution,[],[f3805,f110])).
% 8.72/1.48  fof(f3805,plain,(
% 8.72/1.48    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | (spl10_25 | ~spl10_73)),
% 8.72/1.48    inference(forward_demodulation,[],[f1862,f3701])).
% 8.72/1.48  fof(f1862,plain,(
% 8.72/1.48    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | ~v1_xboole_0(sK5) | spl10_25),
% 8.72/1.48    inference(resolution,[],[f701,f1330])).
% 8.72/1.48  fof(f1330,plain,(
% 8.72/1.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) | spl10_25),
% 8.72/1.48    inference(avatar_component_clause,[],[f1328])).
% 8.72/1.48  fof(f2324,plain,(
% 8.72/1.48    ~spl10_16),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f2313])).
% 8.72/1.48  fof(f2313,plain,(
% 8.72/1.48    $false | ~spl10_16),
% 8.72/1.48    inference(subsumption_resolution,[],[f110,f458])).
% 8.72/1.48  fof(f458,plain,(
% 8.72/1.48    ( ! [X6] : (~v1_xboole_0(X6)) ) | ~spl10_16),
% 8.72/1.48    inference(avatar_component_clause,[],[f457])).
% 8.72/1.48  fof(f457,plain,(
% 8.72/1.48    spl10_16 <=> ! [X6] : ~v1_xboole_0(X6)),
% 8.72/1.48    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 8.72/1.48  fof(f1486,plain,(
% 8.72/1.48    spl10_29),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f1485])).
% 8.72/1.48  fof(f1485,plain,(
% 8.72/1.48    $false | spl10_29),
% 8.72/1.48    inference(subsumption_resolution,[],[f1482,f98])).
% 8.72/1.48  fof(f1482,plain,(
% 8.72/1.48    ~l1_pre_topc(sK3) | spl10_29),
% 8.72/1.48    inference(resolution,[],[f1462,f373])).
% 8.72/1.48  fof(f373,plain,(
% 8.72/1.48    ( ! [X5] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))) | ~l1_pre_topc(X5)) )),
% 8.72/1.48    inference(resolution,[],[f134,f112])).
% 8.72/1.48  fof(f112,plain,(
% 8.72/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f32])).
% 8.72/1.48  fof(f32,plain,(
% 8.72/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.72/1.48    inference(ennf_transformation,[],[f24])).
% 8.72/1.48  fof(f24,axiom,(
% 8.72/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 8.72/1.48  fof(f134,plain,(
% 8.72/1.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 8.72/1.48    inference(cnf_transformation,[],[f47])).
% 8.72/1.48  fof(f47,plain,(
% 8.72/1.48    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.72/1.48    inference(ennf_transformation,[],[f23])).
% 8.72/1.48  fof(f23,axiom,(
% 8.72/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 8.72/1.48  fof(f1462,plain,(
% 8.72/1.48    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | spl10_29),
% 8.72/1.48    inference(avatar_component_clause,[],[f1460])).
% 8.72/1.48  fof(f1481,plain,(
% 8.72/1.48    spl10_28),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f1480])).
% 8.72/1.48  fof(f1480,plain,(
% 8.72/1.48    $false | spl10_28),
% 8.72/1.48    inference(subsumption_resolution,[],[f1479,f97])).
% 8.72/1.48  fof(f1479,plain,(
% 8.72/1.48    ~v2_pre_topc(sK3) | spl10_28),
% 8.72/1.48    inference(subsumption_resolution,[],[f1478,f98])).
% 8.72/1.48  fof(f1478,plain,(
% 8.72/1.48    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl10_28),
% 8.72/1.48    inference(resolution,[],[f1458,f120])).
% 8.72/1.48  fof(f120,plain,(
% 8.72/1.48    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.72/1.48    inference(cnf_transformation,[],[f38])).
% 8.72/1.48  fof(f38,plain,(
% 8.72/1.48    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.72/1.48    inference(flattening,[],[f37])).
% 8.72/1.48  fof(f37,plain,(
% 8.72/1.48    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.72/1.48    inference(ennf_transformation,[],[f25])).
% 8.72/1.48  fof(f25,axiom,(
% 8.72/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 8.72/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 8.72/1.48  fof(f1458,plain,(
% 8.72/1.48    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | spl10_28),
% 8.72/1.48    inference(avatar_component_clause,[],[f1456])).
% 8.72/1.48  fof(f1350,plain,(
% 8.72/1.48    spl10_24),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f1349])).
% 8.72/1.48  fof(f1349,plain,(
% 8.72/1.48    $false | spl10_24),
% 8.72/1.48    inference(subsumption_resolution,[],[f1346,f100])).
% 8.72/1.48  fof(f1346,plain,(
% 8.72/1.48    ~l1_pre_topc(sK4) | spl10_24),
% 8.72/1.48    inference(resolution,[],[f1326,f373])).
% 8.72/1.48  fof(f1326,plain,(
% 8.72/1.48    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | spl10_24),
% 8.72/1.48    inference(avatar_component_clause,[],[f1324])).
% 8.72/1.48  fof(f1345,plain,(
% 8.72/1.48    spl10_23),
% 8.72/1.48    inference(avatar_contradiction_clause,[],[f1344])).
% 8.72/1.48  fof(f1344,plain,(
% 8.72/1.48    $false | spl10_23),
% 8.72/1.48    inference(subsumption_resolution,[],[f1343,f99])).
% 8.72/1.48  fof(f1343,plain,(
% 8.72/1.48    ~v2_pre_topc(sK4) | spl10_23),
% 8.72/1.48    inference(subsumption_resolution,[],[f1342,f100])).
% 8.72/1.48  fof(f1342,plain,(
% 8.72/1.48    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | spl10_23),
% 8.72/1.48    inference(resolution,[],[f1322,f120])).
% 8.72/1.48  fof(f1322,plain,(
% 8.72/1.48    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | spl10_23),
% 8.72/1.48    inference(avatar_component_clause,[],[f1320])).
% 8.72/1.48  fof(f459,plain,(
% 8.72/1.48    spl10_15 | spl10_16),
% 8.72/1.48    inference(avatar_split_clause,[],[f441,f457,f454])).
% 8.72/1.48  fof(f441,plain,(
% 8.72/1.48    ( ! [X6,X7] : (~v1_xboole_0(X6) | ~r2_hidden(X7,k1_xboole_0)) )),
% 8.72/1.48    inference(resolution,[],[f163,f111])).
% 8.72/1.48  fof(f190,plain,(
% 8.72/1.48    spl10_1 | spl10_2),
% 8.72/1.48    inference(avatar_split_clause,[],[f108,f186,f182])).
% 8.72/1.48  fof(f108,plain,(
% 8.72/1.48    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  fof(f189,plain,(
% 8.72/1.48    ~spl10_1 | ~spl10_2),
% 8.72/1.48    inference(avatar_split_clause,[],[f109,f186,f182])).
% 8.72/1.48  fof(f109,plain,(
% 8.72/1.48    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)),
% 8.72/1.48    inference(cnf_transformation,[],[f76])).
% 8.72/1.48  % SZS output end Proof for theBenchmark
% 8.72/1.48  % (32632)------------------------------
% 8.72/1.48  % (32632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.72/1.48  % (32632)Termination reason: Refutation
% 8.72/1.48  
% 8.72/1.48  % (32632)Memory used [KB]: 10874
% 8.72/1.48  % (32632)Time elapsed: 1.033 s
% 8.72/1.48  % (32632)------------------------------
% 8.72/1.48  % (32632)------------------------------
% 8.72/1.48  % (32604)Success in time 1.105 s
%------------------------------------------------------------------------------
