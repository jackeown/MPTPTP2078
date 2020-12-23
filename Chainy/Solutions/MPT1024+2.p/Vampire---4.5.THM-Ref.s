%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1024+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 23.02s
% Output     : Refutation 23.25s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 185 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  320 ( 560 expanded)
%              Number of equality atoms :   56 (  84 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4500,f4592,f4603,f5038,f5042,f5051,f9369,f10485,f11361,f12344,f14420,f14458,f15008,f15072])).

fof(f15072,plain,
    ( ~ spl328_1
    | ~ spl328_6
    | ~ spl328_44
    | ~ spl328_66
    | ~ spl328_88
    | ~ spl328_106 ),
    inference(avatar_contradiction_clause,[],[f15071])).

fof(f15071,plain,
    ( $false
    | ~ spl328_1
    | ~ spl328_6
    | ~ spl328_44
    | ~ spl328_66
    | ~ spl328_88
    | ~ spl328_106 ),
    inference(subsumption_resolution,[],[f15014,f13271])).

fof(f13271,plain,
    ( ~ r2_hidden(sK126(sK4,sK2,sK3),sK0)
    | ~ spl328_1
    | ~ spl328_6
    | ~ spl328_44
    | ~ spl328_88 ),
    inference(subsumption_resolution,[],[f10071,f13270])).

fof(f13270,plain,
    ( sK4 = k1_funct_1(sK3,sK126(sK4,sK2,sK3))
    | ~ spl328_1
    | ~ spl328_6
    | ~ spl328_88 ),
    inference(subsumption_resolution,[],[f13269,f5037])).

fof(f5037,plain,
    ( v1_relat_1(sK3)
    | ~ spl328_6 ),
    inference(avatar_component_clause,[],[f5036])).

fof(f5036,plain,
    ( spl328_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_6])])).

fof(f13269,plain,
    ( sK4 = k1_funct_1(sK3,sK126(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl328_1
    | ~ spl328_88 ),
    inference(subsumption_resolution,[],[f13155,f4499])).

fof(f4499,plain,
    ( v1_funct_1(sK3)
    | ~ spl328_1 ),
    inference(avatar_component_clause,[],[f4498])).

fof(f4498,plain,
    ( spl328_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_1])])).

fof(f13155,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK126(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl328_88 ),
    inference(resolution,[],[f12343,f2662])).

fof(f2662,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1605])).

fof(f1605,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1604])).

fof(f1604,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1050])).

fof(f1050,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f12343,plain,
    ( r2_hidden(k4_tarski(sK126(sK4,sK2,sK3),sK4),sK3)
    | ~ spl328_88 ),
    inference(avatar_component_clause,[],[f12342])).

fof(f12342,plain,
    ( spl328_88
  <=> r2_hidden(k4_tarski(sK126(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_88])])).

fof(f10071,plain,
    ( ~ r2_hidden(sK126(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK126(sK4,sK2,sK3))
    | ~ spl328_44 ),
    inference(resolution,[],[f9368,f2647])).

fof(f2647,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f1593])).

fof(f1593,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1592])).

fof(f1592,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1509])).

fof(f1509,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f1508])).

fof(f1508,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f9368,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),sK2)
    | ~ spl328_44 ),
    inference(avatar_component_clause,[],[f9367])).

fof(f9367,plain,
    ( spl328_44
  <=> r2_hidden(sK126(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_44])])).

fof(f15014,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),sK0)
    | ~ spl328_66
    | ~ spl328_106 ),
    inference(superposition,[],[f11360,f14480])).

fof(f14480,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl328_106 ),
    inference(avatar_component_clause,[],[f14479])).

fof(f14479,plain,
    ( spl328_106
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_106])])).

fof(f11360,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl328_66 ),
    inference(avatar_component_clause,[],[f11359])).

fof(f11359,plain,
    ( spl328_66
  <=> r2_hidden(sK126(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_66])])).

fof(f15008,plain,
    ( spl328_106
    | ~ spl328_56
    | ~ spl328_102 ),
    inference(avatar_split_clause,[],[f14506,f14418,f10483,f14479])).

fof(f10483,plain,
    ( spl328_56
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_56])])).

fof(f14418,plain,
    ( spl328_102
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_102])])).

fof(f14506,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl328_56
    | ~ spl328_102 ),
    inference(superposition,[],[f14419,f10484])).

fof(f10484,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl328_56 ),
    inference(avatar_component_clause,[],[f10483])).

fof(f14419,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl328_102 ),
    inference(avatar_component_clause,[],[f14418])).

fof(f14458,plain,
    ( ~ spl328_5
    | ~ spl328_9
    | ~ spl328_46 ),
    inference(avatar_contradiction_clause,[],[f14457])).

fof(f14457,plain,
    ( $false
    | ~ spl328_5
    | ~ spl328_9
    | ~ spl328_46 ),
    inference(subsumption_resolution,[],[f12104,f14456])).

fof(f14456,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_tarski(k1_xboole_0))
    | ~ spl328_5
    | ~ spl328_46 ),
    inference(forward_demodulation,[],[f14435,f2908])).

fof(f2908,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f14435,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl328_5
    | ~ spl328_46 ),
    inference(superposition,[],[f4768,f9589])).

fof(f9589,plain,
    ( k1_xboole_0 = sK1
    | ~ spl328_46 ),
    inference(avatar_component_clause,[],[f9588])).

fof(f9588,plain,
    ( spl328_46
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_46])])).

fof(f4768,plain,
    ( ! [X9] : m1_subset_1(k9_relat_1(sK3,X9),k1_zfmisc_1(sK1))
    | ~ spl328_5 ),
    inference(forward_demodulation,[],[f4613,f4612])).

fof(f4612,plain,
    ( ! [X8] : k7_relset_1(sK0,sK1,sK3,X8) = k9_relat_1(sK3,X8)
    | ~ spl328_5 ),
    inference(resolution,[],[f4602,f2872])).

fof(f2872,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f1721,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f4602,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl328_5 ),
    inference(avatar_component_clause,[],[f4601])).

fof(f4601,plain,
    ( spl328_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_5])])).

fof(f4613,plain,
    ( ! [X9] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X9),k1_zfmisc_1(sK1))
    | ~ spl328_5 ),
    inference(resolution,[],[f4602,f2873])).

fof(f2873,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1722])).

fof(f1722,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1221])).

fof(f1221,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f12104,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_tarski(k1_xboole_0))
    | ~ spl328_9 ),
    inference(subsumption_resolution,[],[f12103,f3703])).

fof(f3703,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f12103,plain,
    ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_tarski(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl328_9 ),
    inference(superposition,[],[f5128,f2908])).

fof(f5128,plain,
    ( ! [X70] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X70))
        | ~ v1_xboole_0(X70) )
    | ~ spl328_9 ),
    inference(resolution,[],[f5050,f3671])).

fof(f3671,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f2257])).

fof(f2257,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f5050,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl328_9 ),
    inference(avatar_component_clause,[],[f5049])).

fof(f5049,plain,
    ( spl328_9
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_9])])).

fof(f14420,plain,
    ( spl328_102
    | spl328_46
    | ~ spl328_2
    | ~ spl328_5 ),
    inference(avatar_split_clause,[],[f4982,f4601,f4590,f9588,f14418])).

fof(f4590,plain,
    ( spl328_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_2])])).

fof(f4982,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl328_2
    | ~ spl328_5 ),
    inference(subsumption_resolution,[],[f4698,f4591])).

fof(f4591,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl328_2 ),
    inference(avatar_component_clause,[],[f4590])).

fof(f4698,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl328_5 ),
    inference(resolution,[],[f4602,f3847])).

fof(f3847,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f2393])).

fof(f2393,plain,(
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
    inference(flattening,[],[f2392])).

fof(f2392,plain,(
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
    inference(ennf_transformation,[],[f1476])).

fof(f1476,axiom,(
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

fof(f12344,plain,
    ( spl328_88
    | ~ spl328_6
    | ~ spl328_9 ),
    inference(avatar_split_clause,[],[f5155,f5049,f5036,f12342])).

fof(f5155,plain,
    ( r2_hidden(k4_tarski(sK126(sK4,sK2,sK3),sK4),sK3)
    | ~ spl328_6
    | ~ spl328_9 ),
    inference(subsumption_resolution,[],[f5058,f5037])).

fof(f5058,plain,
    ( r2_hidden(k4_tarski(sK126(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl328_9 ),
    inference(resolution,[],[f5050,f3361])).

fof(f3361,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK126(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2034,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f745])).

fof(f745,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f11361,plain,
    ( spl328_66
    | ~ spl328_6
    | ~ spl328_9 ),
    inference(avatar_split_clause,[],[f5154,f5049,f5036,f11359])).

fof(f5154,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl328_6
    | ~ spl328_9 ),
    inference(subsumption_resolution,[],[f5057,f5037])).

fof(f5057,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl328_9 ),
    inference(resolution,[],[f5050,f3360])).

fof(f3360,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK126(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f10485,plain,
    ( spl328_56
    | ~ spl328_5 ),
    inference(avatar_split_clause,[],[f4700,f4601,f10483])).

fof(f4700,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl328_5 ),
    inference(resolution,[],[f4602,f3849])).

fof(f3849,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2395])).

fof(f2395,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f9369,plain,
    ( spl328_44
    | ~ spl328_6
    | ~ spl328_9 ),
    inference(avatar_split_clause,[],[f5156,f5049,f5036,f9367])).

fof(f5156,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),sK2)
    | ~ spl328_6
    | ~ spl328_9 ),
    inference(subsumption_resolution,[],[f5059,f5037])).

fof(f5059,plain,
    ( r2_hidden(sK126(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl328_9 ),
    inference(resolution,[],[f5050,f3362])).

fof(f3362,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK126(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f5051,plain,
    ( spl328_9
    | ~ spl328_5
    | ~ spl328_7 ),
    inference(avatar_split_clause,[],[f5043,f5040,f4601,f5049])).

fof(f5040,plain,
    ( spl328_7
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl328_7])])).

fof(f5043,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl328_5
    | ~ spl328_7 ),
    inference(forward_demodulation,[],[f5041,f4612])).

fof(f5041,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl328_7 ),
    inference(avatar_component_clause,[],[f5040])).

fof(f5042,plain,(
    spl328_7 ),
    inference(avatar_split_clause,[],[f2648,f5040])).

fof(f2648,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f1593])).

fof(f5038,plain,
    ( spl328_6
    | ~ spl328_5 ),
    inference(avatar_split_clause,[],[f4624,f4601,f5036])).

fof(f4624,plain,
    ( v1_relat_1(sK3)
    | ~ spl328_5 ),
    inference(resolution,[],[f4602,f2893])).

fof(f2893,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1741])).

fof(f1741,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4603,plain,(
    spl328_5 ),
    inference(avatar_split_clause,[],[f2651,f4601])).

fof(f2651,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1593])).

fof(f4592,plain,(
    spl328_2 ),
    inference(avatar_split_clause,[],[f2650,f4590])).

fof(f2650,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f1593])).

fof(f4500,plain,(
    spl328_1 ),
    inference(avatar_split_clause,[],[f2649,f4498])).

fof(f2649,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f1593])).
%------------------------------------------------------------------------------
