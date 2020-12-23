%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:10 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 385 expanded)
%              Number of leaves         :   43 ( 157 expanded)
%              Depth                    :   12
%              Number of atoms          :  443 ( 848 expanded)
%              Number of equality atoms :  142 ( 302 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f143,f151,f167,f218,f227,f251,f589,f777,f906,f982,f989,f994,f1008,f1041,f1074,f1082,f1113,f1306])).

fof(f1306,plain,
    ( spl5_76
    | ~ spl5_32
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1305,f645,f391,f1110])).

fof(f1110,plain,
    ( spl5_76
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f391,plain,
    ( spl5_32
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f645,plain,
    ( spl5_54
  <=> ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1305,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl5_32
    | ~ spl5_54 ),
    inference(trivial_inequality_removal,[],[f1304])).

fof(f1304,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl5_32
    | ~ spl5_54 ),
    inference(superposition,[],[f646,f393])).

fof(f393,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f391])).

fof(f646,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f645])).

fof(f1113,plain,
    ( ~ spl5_76
    | spl5_1
    | ~ spl5_32
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f1108,f666,f391,f109,f1110])).

fof(f109,plain,
    ( spl5_1
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f666,plain,
    ( spl5_55
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f1108,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl5_1
    | ~ spl5_32
    | ~ spl5_55 ),
    inference(forward_demodulation,[],[f1097,f668])).

fof(f668,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f666])).

fof(f1097,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl5_1
    | ~ spl5_32 ),
    inference(backward_demodulation,[],[f111,f393])).

fof(f111,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1082,plain,
    ( spl5_24
    | spl5_32
    | ~ spl5_7
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f1077,f334,f140,f391,f279])).

fof(f279,plain,
    ( spl5_24
  <=> o_0_0_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f140,plain,
    ( spl5_7
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f334,plain,
    ( spl5_31
  <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1077,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_7
    | ~ spl5_31 ),
    inference(resolution,[],[f336,f413])).

fof(f413,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
        | k2_enumset1(X1,X1,X1,X1) = X0
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f96,f142])).

fof(f142,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f67,f89,f89])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f336,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f334])).

fof(f1074,plain,
    ( ~ spl5_18
    | spl5_31
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1073,f243,f334,f248])).

fof(f248,plain,
    ( spl5_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f243,plain,
    ( spl5_17
  <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1073,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f245,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f245,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1041,plain,
    ( spl5_17
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1030,f119,f243])).

fof(f119,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1030,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f121,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1008,plain,
    ( spl5_55
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f997,f556,f666])).

fof(f556,plain,
    ( spl5_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f997,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ spl5_46 ),
    inference(resolution,[],[f558,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f558,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f556])).

fof(f994,plain,
    ( spl5_22
    | ~ spl5_24
    | ~ spl5_7
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f991,f248,f140,f279,f270])).

fof(f270,plain,
    ( spl5_22
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f991,plain,
    ( o_0_0_xboole_0 != k1_relat_1(sK2)
    | o_0_0_xboole_0 = sK2
    | ~ spl5_7
    | ~ spl5_18 ),
    inference(resolution,[],[f250,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | o_0_0_xboole_0 != k1_relat_1(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f181,f142])).

fof(f181,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f55,f142])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f250,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f248])).

fof(f989,plain,
    ( spl5_54
    | ~ spl5_18
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f988,f129,f248,f645])).

fof(f129,plain,
    ( spl5_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f988,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f131,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f60,f89,f89])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f131,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f982,plain,
    ( spl5_46
    | ~ spl5_3
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f551,f391,f119,f556])).

fof(f551,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_3
    | ~ spl5_32 ),
    inference(backward_demodulation,[],[f121,f393])).

fof(f906,plain,
    ( spl5_8
    | spl5_65
    | ~ spl5_7
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f902,f432,f140,f774,f148])).

fof(f148,plain,
    ( spl5_8
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f774,plain,
    ( spl5_65
  <=> o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f432,plain,
    ( spl5_35
  <=> v1_funct_2(o_0_0_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f902,plain,
    ( o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | o_0_0_xboole_0 = sK1
    | ~ spl5_7
    | ~ spl5_35 ),
    inference(resolution,[],[f898,f434])).

fof(f434,plain,
    ( v1_funct_2(o_0_0_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f432])).

fof(f898,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(o_0_0_xboole_0,X3,X2)
        | o_0_0_xboole_0 = X3
        | o_0_0_xboole_0 = X2 )
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f511,f896])).

fof(f896,plain,
    ( ! [X2,X3] : o_0_0_xboole_0 = k1_relset_1(X2,X3,o_0_0_xboole_0)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f541,f835])).

fof(f835,plain,
    ( ! [X2,X3,X1] : o_0_0_xboole_0 = k8_relset_1(X1,X2,o_0_0_xboole_0,X3)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f342,f811])).

fof(f811,plain,
    ( ! [X4] : o_0_0_xboole_0 = k10_relat_1(o_0_0_xboole_0,X4)
    | ~ spl5_7 ),
    inference(resolution,[],[f782,f197])).

fof(f197,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X1 )
    | ~ spl5_7 ),
    inference(resolution,[],[f63,f154])).

fof(f154,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl5_7 ),
    inference(resolution,[],[f71,f145])).

fof(f145,plain,
    ( ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f52,f142])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f782,plain,
    ( ! [X5,X3] : r1_tarski(k10_relat_1(o_0_0_xboole_0,X5),X3)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f368,f342])).

fof(f368,plain,
    ( ! [X4,X5,X3] : r1_tarski(k8_relset_1(X3,X4,o_0_0_xboole_0,X5),X3)
    | ~ spl5_7 ),
    inference(resolution,[],[f339,f71])).

fof(f339,plain,
    ( ! [X2,X3,X1] : m1_subset_1(k8_relset_1(X1,X2,o_0_0_xboole_0,X3),k1_zfmisc_1(X1))
    | ~ spl5_7 ),
    inference(resolution,[],[f86,f145])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f342,plain,
    ( ! [X2,X3,X1] : k8_relset_1(X1,X2,o_0_0_xboole_0,X3) = k10_relat_1(o_0_0_xboole_0,X3)
    | ~ spl5_7 ),
    inference(resolution,[],[f87,f145])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f541,plain,
    ( ! [X2,X3] : k8_relset_1(X2,X3,o_0_0_xboole_0,k7_relset_1(X2,X3,o_0_0_xboole_0,X2)) = k1_relset_1(X2,X3,o_0_0_xboole_0)
    | ~ spl5_7 ),
    inference(resolution,[],[f77,f145])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f511,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(o_0_0_xboole_0,X3,X2)
        | k1_relset_1(X3,X2,o_0_0_xboole_0) = X3
        | o_0_0_xboole_0 = X2 )
    | ~ spl5_7 ),
    inference(resolution,[],[f498,f145])).

fof(f498,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f83,f142])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f777,plain,
    ( ~ spl5_65
    | ~ spl5_16
    | ~ spl5_22
    | spl5_32 ),
    inference(avatar_split_clause,[],[f772,f391,f270,f224,f774])).

fof(f224,plain,
    ( spl5_16
  <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f772,plain,
    ( o_0_0_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_16
    | ~ spl5_22
    | spl5_32 ),
    inference(forward_demodulation,[],[f771,f226])).

fof(f226,plain,
    ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f224])).

fof(f771,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(o_0_0_xboole_0)
    | ~ spl5_22
    | spl5_32 ),
    inference(forward_demodulation,[],[f392,f272])).

fof(f272,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f270])).

fof(f392,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f391])).

fof(f589,plain,
    ( spl5_35
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f581,f270,f124,f432])).

fof(f124,plain,
    ( spl5_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f581,plain,
    ( v1_funct_2(o_0_0_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f126,f272])).

fof(f126,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f251,plain,
    ( spl5_18
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f239,f119,f248])).

fof(f239,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f121,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f227,plain,
    ( spl5_16
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f222,f216,f140,f224])).

fof(f216,plain,
    ( spl5_15
  <=> ! [X0] : r1_tarski(k1_relat_1(o_0_0_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f222,plain,
    ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(resolution,[],[f217,f197])).

fof(f217,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(o_0_0_xboole_0),X0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f218,plain,
    ( ~ spl5_9
    | spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f214,f140,f216,f164])).

fof(f164,plain,
    ( spl5_9
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f214,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X0)
        | ~ v1_relat_1(o_0_0_xboole_0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f212,f59])).

fof(f212,plain,
    ( ! [X0] : v4_relat_1(o_0_0_xboole_0,X0)
    | ~ spl5_7 ),
    inference(resolution,[],[f75,f145])).

fof(f167,plain,
    ( spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f161,f140,f164])).

fof(f161,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl5_7 ),
    inference(resolution,[],[f73,f145])).

fof(f151,plain,
    ( ~ spl5_8
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f146,f140,f114,f148])).

fof(f114,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f146,plain,
    ( o_0_0_xboole_0 != sK1
    | spl5_2
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f116,f142])).

fof(f116,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f143,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f138,f134,f140])).

fof(f134,plain,
    ( spl5_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f138,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_6 ),
    inference(resolution,[],[f54,f136])).

fof(f136,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f137,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f51,f134])).

fof(f51,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f132,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f46,f129])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f127,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f92,f124])).

fof(f92,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f47,f89])).

fof(f47,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f122,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f91,f119])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f48,f89])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f117,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f114])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f90,f109])).

fof(f90,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f50,f89,f89])).

fof(f50,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:43:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (9194)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (9211)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9190)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9191)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (9197)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (9203)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (9217)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (9188)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9211)Refutation not found, incomplete strategy% (9211)------------------------------
% 0.21/0.54  % (9211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9211)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9211)Memory used [KB]: 10746
% 0.21/0.54  % (9211)Time elapsed: 0.124 s
% 0.21/0.54  % (9211)------------------------------
% 0.21/0.54  % (9211)------------------------------
% 0.21/0.54  % (9192)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (9189)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (9212)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (9200)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (9205)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (9219)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (9208)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (9193)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (9195)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (9206)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (9196)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (9209)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (9199)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (9199)Refutation not found, incomplete strategy% (9199)------------------------------
% 0.21/0.56  % (9199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9218)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (9207)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (9215)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (9213)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (9201)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (9202)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (9204)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (9210)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (9200)Refutation not found, incomplete strategy% (9200)------------------------------
% 0.21/0.57  % (9200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9200)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9200)Memory used [KB]: 10746
% 0.21/0.57  % (9200)Time elapsed: 0.160 s
% 0.21/0.57  % (9200)------------------------------
% 0.21/0.57  % (9200)------------------------------
% 0.21/0.57  % (9210)Refutation not found, incomplete strategy% (9210)------------------------------
% 0.21/0.57  % (9210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9210)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9210)Memory used [KB]: 1791
% 0.21/0.57  % (9210)Time elapsed: 0.158 s
% 0.21/0.57  % (9210)------------------------------
% 0.21/0.57  % (9210)------------------------------
% 0.21/0.57  % (9214)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (9199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9199)Memory used [KB]: 10618
% 0.21/0.57  % (9199)Time elapsed: 0.149 s
% 0.21/0.57  % (9199)------------------------------
% 0.21/0.57  % (9199)------------------------------
% 0.21/0.58  % (9209)Refutation not found, incomplete strategy% (9209)------------------------------
% 0.21/0.58  % (9209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (9196)Refutation not found, incomplete strategy% (9196)------------------------------
% 0.21/0.59  % (9196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (9209)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (9209)Memory used [KB]: 10874
% 0.21/0.59  % (9209)Time elapsed: 0.170 s
% 0.21/0.59  % (9209)------------------------------
% 0.21/0.59  % (9209)------------------------------
% 1.70/0.59  % (9206)Refutation not found, incomplete strategy% (9206)------------------------------
% 1.70/0.59  % (9206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (9206)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (9206)Memory used [KB]: 10746
% 1.70/0.59  % (9206)Time elapsed: 0.177 s
% 1.70/0.59  % (9206)------------------------------
% 1.70/0.59  % (9206)------------------------------
% 1.70/0.60  % (9205)Refutation found. Thanks to Tanya!
% 1.70/0.60  % SZS status Theorem for theBenchmark
% 1.70/0.60  % (9196)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (9196)Memory used [KB]: 11001
% 1.70/0.60  % (9196)Time elapsed: 0.158 s
% 1.70/0.60  % (9196)------------------------------
% 1.70/0.60  % (9196)------------------------------
% 1.82/0.61  % SZS output start Proof for theBenchmark
% 1.82/0.62  fof(f1307,plain,(
% 1.82/0.62    $false),
% 1.82/0.62    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f143,f151,f167,f218,f227,f251,f589,f777,f906,f982,f989,f994,f1008,f1041,f1074,f1082,f1113,f1306])).
% 1.82/0.62  fof(f1306,plain,(
% 1.82/0.62    spl5_76 | ~spl5_32 | ~spl5_54),
% 1.82/0.62    inference(avatar_split_clause,[],[f1305,f645,f391,f1110])).
% 1.82/0.62  fof(f1110,plain,(
% 1.82/0.62    spl5_76 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 1.82/0.62  fof(f391,plain,(
% 1.82/0.62    spl5_32 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.82/0.62  fof(f645,plain,(
% 1.82/0.62    spl5_54 <=> ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 1.82/0.62  fof(f1305,plain,(
% 1.82/0.62    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | (~spl5_32 | ~spl5_54)),
% 1.82/0.62    inference(trivial_inequality_removal,[],[f1304])).
% 1.82/0.62  fof(f1304,plain,(
% 1.82/0.62    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | (~spl5_32 | ~spl5_54)),
% 1.82/0.62    inference(superposition,[],[f646,f393])).
% 1.82/0.62  fof(f393,plain,(
% 1.82/0.62    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl5_32),
% 1.82/0.62    inference(avatar_component_clause,[],[f391])).
% 1.82/0.62  fof(f646,plain,(
% 1.82/0.62    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) ) | ~spl5_54),
% 1.82/0.62    inference(avatar_component_clause,[],[f645])).
% 1.82/0.62  fof(f1113,plain,(
% 1.82/0.62    ~spl5_76 | spl5_1 | ~spl5_32 | ~spl5_55),
% 1.82/0.62    inference(avatar_split_clause,[],[f1108,f666,f391,f109,f1110])).
% 1.82/0.62  fof(f109,plain,(
% 1.82/0.62    spl5_1 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.82/0.62  fof(f666,plain,(
% 1.82/0.62    spl5_55 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.82/0.62  fof(f1108,plain,(
% 1.82/0.62    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | (spl5_1 | ~spl5_32 | ~spl5_55)),
% 1.82/0.62    inference(forward_demodulation,[],[f1097,f668])).
% 1.82/0.62  fof(f668,plain,(
% 1.82/0.62    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~spl5_55),
% 1.82/0.62    inference(avatar_component_clause,[],[f666])).
% 1.82/0.62  fof(f1097,plain,(
% 1.82/0.62    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl5_1 | ~spl5_32)),
% 1.82/0.62    inference(backward_demodulation,[],[f111,f393])).
% 1.82/0.62  fof(f111,plain,(
% 1.82/0.62    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl5_1),
% 1.82/0.62    inference(avatar_component_clause,[],[f109])).
% 1.82/0.62  fof(f1082,plain,(
% 1.82/0.62    spl5_24 | spl5_32 | ~spl5_7 | ~spl5_31),
% 1.82/0.62    inference(avatar_split_clause,[],[f1077,f334,f140,f391,f279])).
% 1.82/0.62  fof(f279,plain,(
% 1.82/0.62    spl5_24 <=> o_0_0_xboole_0 = k1_relat_1(sK2)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.82/0.62  fof(f140,plain,(
% 1.82/0.62    spl5_7 <=> o_0_0_xboole_0 = k1_xboole_0),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.82/0.62  fof(f334,plain,(
% 1.82/0.62    spl5_31 <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.82/0.62  fof(f1077,plain,(
% 1.82/0.62    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2) | (~spl5_7 | ~spl5_31)),
% 1.82/0.62    inference(resolution,[],[f336,f413])).
% 1.82/0.62  fof(f413,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0) ) | ~spl5_7),
% 1.82/0.62    inference(forward_demodulation,[],[f96,f142])).
% 1.82/0.62  fof(f142,plain,(
% 1.82/0.62    o_0_0_xboole_0 = k1_xboole_0 | ~spl5_7),
% 1.82/0.62    inference(avatar_component_clause,[],[f140])).
% 1.82/0.62  fof(f96,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.82/0.62    inference(definition_unfolding,[],[f67,f89,f89])).
% 1.82/0.62  fof(f89,plain,(
% 1.82/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.82/0.62    inference(definition_unfolding,[],[f53,f88])).
% 1.82/0.62  fof(f88,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.82/0.62    inference(definition_unfolding,[],[f57,f72])).
% 1.82/0.62  fof(f72,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f7])).
% 1.82/0.62  fof(f7,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.82/0.62  fof(f57,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f6])).
% 1.82/0.62  fof(f6,axiom,(
% 1.82/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.62  fof(f53,plain,(
% 1.82/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f5])).
% 1.82/0.62  fof(f5,axiom,(
% 1.82/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.82/0.62  fof(f67,plain,(
% 1.82/0.62    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f8])).
% 1.82/0.62  fof(f8,axiom,(
% 1.82/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.82/0.62  fof(f336,plain,(
% 1.82/0.62    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_31),
% 1.82/0.62    inference(avatar_component_clause,[],[f334])).
% 1.82/0.62  fof(f1074,plain,(
% 1.82/0.62    ~spl5_18 | spl5_31 | ~spl5_17),
% 1.82/0.62    inference(avatar_split_clause,[],[f1073,f243,f334,f248])).
% 1.82/0.62  fof(f248,plain,(
% 1.82/0.62    spl5_18 <=> v1_relat_1(sK2)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.82/0.62  fof(f243,plain,(
% 1.82/0.62    spl5_17 <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.82/0.62  fof(f1073,plain,(
% 1.82/0.62    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK2) | ~spl5_17),
% 1.82/0.62    inference(resolution,[],[f245,f59])).
% 1.82/0.62  fof(f59,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f31])).
% 1.82/0.62  fof(f31,plain,(
% 1.82/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.82/0.62    inference(ennf_transformation,[],[f13])).
% 1.82/0.62  fof(f13,axiom,(
% 1.82/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.82/0.62  fof(f245,plain,(
% 1.82/0.62    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_17),
% 1.82/0.62    inference(avatar_component_clause,[],[f243])).
% 1.82/0.62  fof(f1041,plain,(
% 1.82/0.62    spl5_17 | ~spl5_3),
% 1.82/0.62    inference(avatar_split_clause,[],[f1030,f119,f243])).
% 1.82/0.62  fof(f119,plain,(
% 1.82/0.62    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.82/0.62  fof(f1030,plain,(
% 1.82/0.62    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_3),
% 1.82/0.62    inference(resolution,[],[f121,f75])).
% 1.82/0.62  fof(f75,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f37])).
% 1.82/0.62  fof(f37,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(ennf_transformation,[],[f25])).
% 1.82/0.62  fof(f25,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.82/0.62    inference(pure_predicate_removal,[],[f17])).
% 1.82/0.62  fof(f17,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.82/0.62  fof(f121,plain,(
% 1.82/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl5_3),
% 1.82/0.62    inference(avatar_component_clause,[],[f119])).
% 1.82/0.62  fof(f1008,plain,(
% 1.82/0.62    spl5_55 | ~spl5_46),
% 1.82/0.62    inference(avatar_split_clause,[],[f997,f556,f666])).
% 1.82/0.62  fof(f556,plain,(
% 1.82/0.62    spl5_46 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 1.82/0.62  fof(f997,plain,(
% 1.82/0.62    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~spl5_46),
% 1.82/0.62    inference(resolution,[],[f558,f74])).
% 1.82/0.62  fof(f74,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f36])).
% 1.82/0.62  fof(f36,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(ennf_transformation,[],[f19])).
% 1.82/0.62  fof(f19,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.82/0.62  fof(f558,plain,(
% 1.82/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl5_46),
% 1.82/0.62    inference(avatar_component_clause,[],[f556])).
% 1.82/0.62  fof(f994,plain,(
% 1.82/0.62    spl5_22 | ~spl5_24 | ~spl5_7 | ~spl5_18),
% 1.82/0.62    inference(avatar_split_clause,[],[f991,f248,f140,f279,f270])).
% 1.82/0.62  fof(f270,plain,(
% 1.82/0.62    spl5_22 <=> o_0_0_xboole_0 = sK2),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.82/0.62  fof(f991,plain,(
% 1.82/0.62    o_0_0_xboole_0 != k1_relat_1(sK2) | o_0_0_xboole_0 = sK2 | (~spl5_7 | ~spl5_18)),
% 1.82/0.62    inference(resolution,[],[f250,f182])).
% 1.82/0.62  fof(f182,plain,(
% 1.82/0.62    ( ! [X0] : (~v1_relat_1(X0) | o_0_0_xboole_0 != k1_relat_1(X0) | o_0_0_xboole_0 = X0) ) | ~spl5_7),
% 1.82/0.62    inference(forward_demodulation,[],[f181,f142])).
% 1.82/0.62  fof(f181,plain,(
% 1.82/0.62    ( ! [X0] : (o_0_0_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl5_7),
% 1.82/0.62    inference(forward_demodulation,[],[f55,f142])).
% 1.82/0.62  fof(f55,plain,(
% 1.82/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.82/0.62    inference(cnf_transformation,[],[f30])).
% 1.82/0.62  fof(f30,plain,(
% 1.82/0.62    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.82/0.62    inference(flattening,[],[f29])).
% 1.82/0.62  fof(f29,plain,(
% 1.82/0.62    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.82/0.62    inference(ennf_transformation,[],[f14])).
% 1.82/0.62  fof(f14,axiom,(
% 1.82/0.62    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.82/0.62  fof(f250,plain,(
% 1.82/0.62    v1_relat_1(sK2) | ~spl5_18),
% 1.82/0.62    inference(avatar_component_clause,[],[f248])).
% 1.82/0.62  fof(f989,plain,(
% 1.82/0.62    spl5_54 | ~spl5_18 | ~spl5_5),
% 1.82/0.62    inference(avatar_split_clause,[],[f988,f129,f248,f645])).
% 1.82/0.62  fof(f129,plain,(
% 1.82/0.62    spl5_5 <=> v1_funct_1(sK2)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.82/0.62  fof(f988,plain,(
% 1.82/0.62    ( ! [X0] : (~v1_relat_1(sK2) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) ) | ~spl5_5),
% 1.82/0.62    inference(resolution,[],[f131,f93])).
% 1.82/0.62  fof(f93,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.82/0.62    inference(definition_unfolding,[],[f60,f89,f89])).
% 1.82/0.62  fof(f60,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f33])).
% 1.82/0.62  fof(f33,plain,(
% 1.82/0.62    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.82/0.62    inference(flattening,[],[f32])).
% 1.82/0.62  fof(f32,plain,(
% 1.82/0.62    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.82/0.62    inference(ennf_transformation,[],[f15])).
% 1.82/0.62  fof(f15,axiom,(
% 1.82/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.82/0.62  fof(f131,plain,(
% 1.82/0.62    v1_funct_1(sK2) | ~spl5_5),
% 1.82/0.62    inference(avatar_component_clause,[],[f129])).
% 1.82/0.62  fof(f982,plain,(
% 1.82/0.62    spl5_46 | ~spl5_3 | ~spl5_32),
% 1.82/0.62    inference(avatar_split_clause,[],[f551,f391,f119,f556])).
% 1.82/0.62  fof(f551,plain,(
% 1.82/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl5_3 | ~spl5_32)),
% 1.82/0.62    inference(backward_demodulation,[],[f121,f393])).
% 1.82/0.62  fof(f906,plain,(
% 1.82/0.62    spl5_8 | spl5_65 | ~spl5_7 | ~spl5_35),
% 1.82/0.62    inference(avatar_split_clause,[],[f902,f432,f140,f774,f148])).
% 1.82/0.62  fof(f148,plain,(
% 1.82/0.62    spl5_8 <=> o_0_0_xboole_0 = sK1),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.82/0.62  fof(f774,plain,(
% 1.82/0.62    spl5_65 <=> o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 1.82/0.62  fof(f432,plain,(
% 1.82/0.62    spl5_35 <=> v1_funct_2(o_0_0_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.82/0.62  fof(f902,plain,(
% 1.82/0.62    o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | o_0_0_xboole_0 = sK1 | (~spl5_7 | ~spl5_35)),
% 1.82/0.62    inference(resolution,[],[f898,f434])).
% 1.82/0.62  fof(f434,plain,(
% 1.82/0.62    v1_funct_2(o_0_0_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl5_35),
% 1.82/0.62    inference(avatar_component_clause,[],[f432])).
% 1.82/0.62  fof(f898,plain,(
% 1.82/0.62    ( ! [X2,X3] : (~v1_funct_2(o_0_0_xboole_0,X3,X2) | o_0_0_xboole_0 = X3 | o_0_0_xboole_0 = X2) ) | ~spl5_7),
% 1.82/0.62    inference(backward_demodulation,[],[f511,f896])).
% 1.82/0.62  fof(f896,plain,(
% 1.82/0.62    ( ! [X2,X3] : (o_0_0_xboole_0 = k1_relset_1(X2,X3,o_0_0_xboole_0)) ) | ~spl5_7),
% 1.82/0.62    inference(forward_demodulation,[],[f541,f835])).
% 1.82/0.62  fof(f835,plain,(
% 1.82/0.62    ( ! [X2,X3,X1] : (o_0_0_xboole_0 = k8_relset_1(X1,X2,o_0_0_xboole_0,X3)) ) | ~spl5_7),
% 1.82/0.62    inference(backward_demodulation,[],[f342,f811])).
% 1.82/0.62  fof(f811,plain,(
% 1.82/0.62    ( ! [X4] : (o_0_0_xboole_0 = k10_relat_1(o_0_0_xboole_0,X4)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f782,f197])).
% 1.82/0.62  fof(f197,plain,(
% 1.82/0.62    ( ! [X1] : (~r1_tarski(X1,o_0_0_xboole_0) | o_0_0_xboole_0 = X1) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f63,f154])).
% 1.82/0.62  fof(f154,plain,(
% 1.82/0.62    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f71,f145])).
% 1.82/0.62  fof(f145,plain,(
% 1.82/0.62    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_7),
% 1.82/0.62    inference(backward_demodulation,[],[f52,f142])).
% 1.82/0.62  fof(f52,plain,(
% 1.82/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f9])).
% 1.82/0.62  fof(f9,axiom,(
% 1.82/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.82/0.62  fof(f71,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f10])).
% 1.82/0.62  fof(f10,axiom,(
% 1.82/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.82/0.62  fof(f63,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.82/0.62    inference(cnf_transformation,[],[f4])).
% 1.82/0.62  fof(f4,axiom,(
% 1.82/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.82/0.62  fof(f782,plain,(
% 1.82/0.62    ( ! [X5,X3] : (r1_tarski(k10_relat_1(o_0_0_xboole_0,X5),X3)) ) | ~spl5_7),
% 1.82/0.62    inference(backward_demodulation,[],[f368,f342])).
% 1.82/0.62  fof(f368,plain,(
% 1.82/0.62    ( ! [X4,X5,X3] : (r1_tarski(k8_relset_1(X3,X4,o_0_0_xboole_0,X5),X3)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f339,f71])).
% 1.82/0.62  fof(f339,plain,(
% 1.82/0.62    ( ! [X2,X3,X1] : (m1_subset_1(k8_relset_1(X1,X2,o_0_0_xboole_0,X3),k1_zfmisc_1(X1))) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f86,f145])).
% 1.82/0.62  fof(f86,plain,(
% 1.82/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f44])).
% 1.82/0.62  fof(f44,plain,(
% 1.82/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(ennf_transformation,[],[f18])).
% 1.82/0.62  fof(f18,axiom,(
% 1.82/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.82/0.62  fof(f342,plain,(
% 1.82/0.62    ( ! [X2,X3,X1] : (k8_relset_1(X1,X2,o_0_0_xboole_0,X3) = k10_relat_1(o_0_0_xboole_0,X3)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f87,f145])).
% 1.82/0.62  fof(f87,plain,(
% 1.82/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f45])).
% 1.82/0.62  fof(f45,plain,(
% 1.82/0.62    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(ennf_transformation,[],[f20])).
% 1.82/0.62  fof(f20,axiom,(
% 1.82/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.82/0.62  fof(f541,plain,(
% 1.82/0.62    ( ! [X2,X3] : (k8_relset_1(X2,X3,o_0_0_xboole_0,k7_relset_1(X2,X3,o_0_0_xboole_0,X2)) = k1_relset_1(X2,X3,o_0_0_xboole_0)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f77,f145])).
% 1.82/0.62  fof(f77,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f38])).
% 1.82/0.62  fof(f38,plain,(
% 1.82/0.62    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.82/0.62    inference(ennf_transformation,[],[f21])).
% 1.82/0.62  fof(f21,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 1.82/0.62  fof(f511,plain,(
% 1.82/0.62    ( ! [X2,X3] : (~v1_funct_2(o_0_0_xboole_0,X3,X2) | k1_relset_1(X3,X2,o_0_0_xboole_0) = X3 | o_0_0_xboole_0 = X2) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f498,f145])).
% 1.82/0.62  fof(f498,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | o_0_0_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl5_7),
% 1.82/0.62    inference(forward_demodulation,[],[f83,f142])).
% 1.82/0.62  fof(f83,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f40])).
% 1.82/0.62  fof(f40,plain,(
% 1.82/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(flattening,[],[f39])).
% 1.82/0.62  fof(f39,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(ennf_transformation,[],[f22])).
% 1.82/0.62  fof(f22,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.82/0.62  fof(f777,plain,(
% 1.82/0.62    ~spl5_65 | ~spl5_16 | ~spl5_22 | spl5_32),
% 1.82/0.62    inference(avatar_split_clause,[],[f772,f391,f270,f224,f774])).
% 1.82/0.62  fof(f224,plain,(
% 1.82/0.62    spl5_16 <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.82/0.62  fof(f772,plain,(
% 1.82/0.62    o_0_0_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (~spl5_16 | ~spl5_22 | spl5_32)),
% 1.82/0.62    inference(forward_demodulation,[],[f771,f226])).
% 1.82/0.62  fof(f226,plain,(
% 1.82/0.62    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | ~spl5_16),
% 1.82/0.62    inference(avatar_component_clause,[],[f224])).
% 1.82/0.62  fof(f771,plain,(
% 1.82/0.62    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(o_0_0_xboole_0) | (~spl5_22 | spl5_32)),
% 1.82/0.62    inference(forward_demodulation,[],[f392,f272])).
% 1.82/0.62  fof(f272,plain,(
% 1.82/0.62    o_0_0_xboole_0 = sK2 | ~spl5_22),
% 1.82/0.62    inference(avatar_component_clause,[],[f270])).
% 1.82/0.62  fof(f392,plain,(
% 1.82/0.62    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2) | spl5_32),
% 1.82/0.62    inference(avatar_component_clause,[],[f391])).
% 1.82/0.62  fof(f589,plain,(
% 1.82/0.62    spl5_35 | ~spl5_4 | ~spl5_22),
% 1.82/0.62    inference(avatar_split_clause,[],[f581,f270,f124,f432])).
% 1.82/0.62  fof(f124,plain,(
% 1.82/0.62    spl5_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.82/0.62  fof(f581,plain,(
% 1.82/0.62    v1_funct_2(o_0_0_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl5_4 | ~spl5_22)),
% 1.82/0.62    inference(backward_demodulation,[],[f126,f272])).
% 1.82/0.62  fof(f126,plain,(
% 1.82/0.62    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl5_4),
% 1.82/0.62    inference(avatar_component_clause,[],[f124])).
% 1.82/0.62  fof(f251,plain,(
% 1.82/0.62    spl5_18 | ~spl5_3),
% 1.82/0.62    inference(avatar_split_clause,[],[f239,f119,f248])).
% 1.82/0.62  fof(f239,plain,(
% 1.82/0.62    v1_relat_1(sK2) | ~spl5_3),
% 1.82/0.62    inference(resolution,[],[f121,f73])).
% 1.82/0.62  fof(f73,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f35])).
% 1.82/0.62  fof(f35,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.62    inference(ennf_transformation,[],[f16])).
% 1.82/0.62  fof(f16,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.82/0.62  fof(f227,plain,(
% 1.82/0.62    spl5_16 | ~spl5_7 | ~spl5_15),
% 1.82/0.62    inference(avatar_split_clause,[],[f222,f216,f140,f224])).
% 1.82/0.62  fof(f216,plain,(
% 1.82/0.62    spl5_15 <=> ! [X0] : r1_tarski(k1_relat_1(o_0_0_xboole_0),X0)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.82/0.62  fof(f222,plain,(
% 1.82/0.62    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | (~spl5_7 | ~spl5_15)),
% 1.82/0.62    inference(resolution,[],[f217,f197])).
% 1.82/0.62  fof(f217,plain,(
% 1.82/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(o_0_0_xboole_0),X0)) ) | ~spl5_15),
% 1.82/0.62    inference(avatar_component_clause,[],[f216])).
% 1.82/0.62  fof(f218,plain,(
% 1.82/0.62    ~spl5_9 | spl5_15 | ~spl5_7),
% 1.82/0.62    inference(avatar_split_clause,[],[f214,f140,f216,f164])).
% 1.82/0.62  fof(f164,plain,(
% 1.82/0.62    spl5_9 <=> v1_relat_1(o_0_0_xboole_0)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.82/0.62  fof(f214,plain,(
% 1.82/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(o_0_0_xboole_0),X0) | ~v1_relat_1(o_0_0_xboole_0)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f212,f59])).
% 1.82/0.62  fof(f212,plain,(
% 1.82/0.62    ( ! [X0] : (v4_relat_1(o_0_0_xboole_0,X0)) ) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f75,f145])).
% 1.82/0.62  fof(f167,plain,(
% 1.82/0.62    spl5_9 | ~spl5_7),
% 1.82/0.62    inference(avatar_split_clause,[],[f161,f140,f164])).
% 1.82/0.62  fof(f161,plain,(
% 1.82/0.62    v1_relat_1(o_0_0_xboole_0) | ~spl5_7),
% 1.82/0.62    inference(resolution,[],[f73,f145])).
% 1.82/0.62  fof(f151,plain,(
% 1.82/0.62    ~spl5_8 | spl5_2 | ~spl5_7),
% 1.82/0.62    inference(avatar_split_clause,[],[f146,f140,f114,f148])).
% 1.82/0.62  fof(f114,plain,(
% 1.82/0.62    spl5_2 <=> k1_xboole_0 = sK1),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.82/0.62  fof(f146,plain,(
% 1.82/0.62    o_0_0_xboole_0 != sK1 | (spl5_2 | ~spl5_7)),
% 1.82/0.62    inference(backward_demodulation,[],[f116,f142])).
% 1.82/0.62  fof(f116,plain,(
% 1.82/0.62    k1_xboole_0 != sK1 | spl5_2),
% 1.82/0.62    inference(avatar_component_clause,[],[f114])).
% 1.82/0.62  fof(f143,plain,(
% 1.82/0.62    spl5_7 | ~spl5_6),
% 1.82/0.62    inference(avatar_split_clause,[],[f138,f134,f140])).
% 1.82/0.62  fof(f134,plain,(
% 1.82/0.62    spl5_6 <=> v1_xboole_0(o_0_0_xboole_0)),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.82/0.62  fof(f138,plain,(
% 1.82/0.62    o_0_0_xboole_0 = k1_xboole_0 | ~spl5_6),
% 1.82/0.62    inference(resolution,[],[f54,f136])).
% 1.82/0.62  fof(f136,plain,(
% 1.82/0.62    v1_xboole_0(o_0_0_xboole_0) | ~spl5_6),
% 1.82/0.62    inference(avatar_component_clause,[],[f134])).
% 1.82/0.62  fof(f54,plain,(
% 1.82/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.82/0.62    inference(cnf_transformation,[],[f28])).
% 1.82/0.62  fof(f28,plain,(
% 1.82/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.82/0.62    inference(ennf_transformation,[],[f3])).
% 1.82/0.62  fof(f3,axiom,(
% 1.82/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.82/0.62  fof(f137,plain,(
% 1.82/0.62    spl5_6),
% 1.82/0.62    inference(avatar_split_clause,[],[f51,f134])).
% 1.82/0.62  fof(f51,plain,(
% 1.82/0.62    v1_xboole_0(o_0_0_xboole_0)),
% 1.82/0.62    inference(cnf_transformation,[],[f2])).
% 1.82/0.62  fof(f2,axiom,(
% 1.82/0.62    v1_xboole_0(o_0_0_xboole_0)),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.82/0.62  fof(f132,plain,(
% 1.82/0.62    spl5_5),
% 1.82/0.62    inference(avatar_split_clause,[],[f46,f129])).
% 1.82/0.62  fof(f46,plain,(
% 1.82/0.62    v1_funct_1(sK2)),
% 1.82/0.62    inference(cnf_transformation,[],[f27])).
% 1.82/0.62  fof(f27,plain,(
% 1.82/0.62    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.82/0.62    inference(flattening,[],[f26])).
% 1.82/0.62  fof(f26,plain,(
% 1.82/0.62    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.82/0.62    inference(ennf_transformation,[],[f24])).
% 1.82/0.62  fof(f24,negated_conjecture,(
% 1.82/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.82/0.62    inference(negated_conjecture,[],[f23])).
% 1.82/0.62  fof(f23,conjecture,(
% 1.82/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.82/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 1.82/0.62  fof(f127,plain,(
% 1.82/0.62    spl5_4),
% 1.82/0.62    inference(avatar_split_clause,[],[f92,f124])).
% 1.82/0.62  fof(f92,plain,(
% 1.82/0.62    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.82/0.62    inference(definition_unfolding,[],[f47,f89])).
% 1.82/0.62  fof(f47,plain,(
% 1.82/0.62    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.82/0.62    inference(cnf_transformation,[],[f27])).
% 1.82/0.62  fof(f122,plain,(
% 1.82/0.62    spl5_3),
% 1.82/0.62    inference(avatar_split_clause,[],[f91,f119])).
% 1.82/0.62  fof(f91,plain,(
% 1.82/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.82/0.62    inference(definition_unfolding,[],[f48,f89])).
% 1.82/0.62  fof(f48,plain,(
% 1.82/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.82/0.62    inference(cnf_transformation,[],[f27])).
% 1.82/0.62  fof(f117,plain,(
% 1.82/0.62    ~spl5_2),
% 1.82/0.62    inference(avatar_split_clause,[],[f49,f114])).
% 1.82/0.62  fof(f49,plain,(
% 1.82/0.62    k1_xboole_0 != sK1),
% 1.82/0.62    inference(cnf_transformation,[],[f27])).
% 1.82/0.62  fof(f112,plain,(
% 1.82/0.62    ~spl5_1),
% 1.82/0.62    inference(avatar_split_clause,[],[f90,f109])).
% 1.82/0.62  fof(f90,plain,(
% 1.82/0.62    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.82/0.62    inference(definition_unfolding,[],[f50,f89,f89])).
% 1.82/0.62  fof(f50,plain,(
% 1.82/0.62    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.82/0.62    inference(cnf_transformation,[],[f27])).
% 1.82/0.62  % SZS output end Proof for theBenchmark
% 1.82/0.62  % (9205)------------------------------
% 1.82/0.62  % (9205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (9205)Termination reason: Refutation
% 1.82/0.62  
% 1.82/0.62  % (9205)Memory used [KB]: 11513
% 1.82/0.62  % (9205)Time elapsed: 0.182 s
% 1.82/0.62  % (9205)------------------------------
% 1.82/0.62  % (9205)------------------------------
% 1.82/0.62  % (9184)Success in time 0.251 s
%------------------------------------------------------------------------------
