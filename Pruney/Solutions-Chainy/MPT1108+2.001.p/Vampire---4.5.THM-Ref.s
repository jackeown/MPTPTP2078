%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:04 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 668 expanded)
%              Number of leaves         :   28 ( 183 expanded)
%              Depth                    :   16
%              Number of atoms          :  438 (2531 expanded)
%              Number of equality atoms :   79 ( 200 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f153,f202,f211,f445,f453,f640,f1093,f2151,f3241])).

fof(f3241,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f3231])).

fof(f3231,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f3003,f158,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f143,f144])).

fof(f144,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f61,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_pre_topc)).

fof(f143,plain,(
    ! [X0] : m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f61,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f3003,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK3),k2_zfmisc_1(sK3,u1_struct_0(sK1)))
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f201,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f201,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_5
  <=> m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2151,plain,
    ( ~ spl6_1
    | spl6_4
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f2144])).

fof(f2144,plain,
    ( $false
    | ~ spl6_1
    | spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f145,f1261,f2100,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2100,plain,
    ( sK3 != k1_relat_1(k7_relat_1(sK2,sK3))
    | ~ spl6_1
    | spl6_4 ),
    inference(superposition,[],[f274,f275])).

fof(f275,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f158,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f274,plain,
    ( sK3 != k1_relset_1(sK3,u1_struct_0(sK1),k7_relat_1(sK2,sK3))
    | ~ spl6_1
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f135,f197,f158,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f197,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_4
  <=> v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f135,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_1
  <=> ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1261,plain,
    ( r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f119,f444])).

fof(f444,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl6_12
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f119,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f58,f96])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f61,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1093,plain,
    ( ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f1080])).

fof(f1080,plain,
    ( $false
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f1059,f1051])).

fof(f1051,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f951,f1048])).

fof(f1048,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(X0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f925,f950])).

fof(f950,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f849,f883])).

fof(f883,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f642,f774,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f774,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0))
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f643,f659])).

fof(f659,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f390,f642,f90])).

fof(f390,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl6_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f643,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(sK2,X0))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f180,f390,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f180,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f161,f95])).

fof(f161,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f145,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f642,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f89,f390,f93])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f849,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f669,f825,f100])).

fof(f825,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f775,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f775,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f644,f659])).

fof(f644,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f390,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f669,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f145,f659])).

fof(f925,plain,
    ( ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f747,f883])).

fof(f747,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k1_relset_1(X0,k1_xboole_0,k7_relat_1(k1_xboole_0,X0))
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f473,f659])).

fof(f473,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_relset_1(X0,k1_xboole_0,k7_relat_1(sK2,X0))
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f275,f440])).

fof(f440,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl6_11
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f951,plain,
    ( sK3 != k1_relset_1(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f746,f883])).

fof(f746,plain,
    ( sK3 != k1_relset_1(sK3,k1_xboole_0,k7_relat_1(k1_xboole_0,sK3))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f472,f659])).

fof(f472,plain,
    ( sK3 != k1_relset_1(sK3,k1_xboole_0,k7_relat_1(sK2,sK3))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f274,f440])).

fof(f1059,plain,
    ( k1_xboole_0 = sK3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f89,f952,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(flattening,[],[f38])).

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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f952,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK3,k1_xboole_0)
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f744,f883])).

fof(f744,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK3),sK3,k1_xboole_0)
    | spl6_4
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f462,f659])).

fof(f462,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,k1_xboole_0)
    | spl6_4
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f197,f440])).

fof(f640,plain,
    ( spl6_8
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | spl6_8
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f89,f568,f96])).

fof(f568,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK2))
    | spl6_8
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f524,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f524,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | spl6_8
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f489,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f489,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | spl6_8
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f400,f440])).

fof(f400,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f148,f397,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f397,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f391,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f391,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f389])).

fof(f148,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f61,f96])).

fof(f453,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f148,f436,f95])).

fof(f436,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f445,plain,
    ( ~ spl6_10
    | spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f154,f442,f438,f434])).

fof(f154,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f132,f147])).

fof(f147,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f61,f85])).

fof(f132,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f60,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f211,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f59,f145,f193,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f193,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_3
  <=> v1_funct_1(k7_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f202,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f157,f199,f195,f191])).

fof(f157,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f156,f144])).

fof(f156,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f155,f144])).

fof(f155,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f123,f144])).

fof(f123,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    inference(forward_demodulation,[],[f122,f118])).

fof(f118,plain,(
    sK3 = u1_struct_0(k1_pre_topc(sK0,sK3)) ),
    inference(unit_resulting_resolution,[],[f64,f58,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f57,f118])).

fof(f57,plain,
    ( ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f153,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f139,f61,f68])).

fof(f139,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f140,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f111,f137,f134])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | v1_funct_1(k7_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f59,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (302)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (32746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (32747)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (32743)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (32742)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (32767)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (32754)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (32752)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (32751)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (32764)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (32757)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (32765)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (303)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32758)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (32756)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (32759)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (32744)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (32748)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32749)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (32750)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (32763)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (32762)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (32766)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (32753)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32755)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (300)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (32745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.52/0.56  % (32760)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.56  % (32759)Refutation not found, incomplete strategy% (32759)------------------------------
% 1.52/0.56  % (32759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (32759)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (32759)Memory used [KB]: 10618
% 1.52/0.56  % (32759)Time elapsed: 0.128 s
% 1.52/0.56  % (32759)------------------------------
% 1.52/0.56  % (32759)------------------------------
% 1.52/0.57  % (301)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.61/0.59  % (32761)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.16/0.65  % (32746)Refutation found. Thanks to Tanya!
% 2.16/0.65  % SZS status Theorem for theBenchmark
% 2.16/0.66  % SZS output start Proof for theBenchmark
% 2.16/0.66  fof(f3244,plain,(
% 2.16/0.66    $false),
% 2.16/0.66    inference(avatar_sat_refutation,[],[f140,f153,f202,f211,f445,f453,f640,f1093,f2151,f3241])).
% 2.16/0.66  fof(f3241,plain,(
% 2.16/0.66    spl6_5),
% 2.16/0.66    inference(avatar_contradiction_clause,[],[f3231])).
% 2.16/0.66  fof(f3231,plain,(
% 2.16/0.66    $false | spl6_5),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f3003,f158,f96])).
% 2.16/0.66  fof(f96,plain,(
% 2.16/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f8])).
% 2.16/0.66  fof(f8,axiom,(
% 2.16/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.16/0.66  fof(f158,plain,(
% 2.16/0.66    ( ! [X0] : (m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))) )),
% 2.16/0.66    inference(forward_demodulation,[],[f143,f144])).
% 2.16/0.66  fof(f144,plain,(
% 2.16/0.66    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f61,f67])).
% 2.16/0.66  fof(f67,plain,(
% 2.16/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f34])).
% 2.16/0.66  fof(f34,plain,(
% 2.16/0.66    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.66    inference(ennf_transformation,[],[f20])).
% 2.16/0.66  fof(f20,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.16/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 2.16/0.66  fof(f61,plain,(
% 2.16/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.16/0.66    inference(cnf_transformation,[],[f31])).
% 2.16/0.66  fof(f31,plain,(
% 2.16/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 2.16/0.66    inference(flattening,[],[f30])).
% 2.16/0.66  fof(f30,plain,(
% 2.16/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 2.16/0.66    inference(ennf_transformation,[],[f29])).
% 2.16/0.67  fof(f29,negated_conjecture,(
% 2.16/0.67    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))))))),
% 2.16/0.67    inference(negated_conjecture,[],[f28])).
% 2.16/0.67  fof(f28,conjecture,(
% 2.16/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_pre_topc)).
% 2.16/0.67  fof(f143,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))) )),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f61,f66])).
% 2.16/0.67  fof(f66,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f33])).
% 2.16/0.67  fof(f33,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.16/0.67    inference(ennf_transformation,[],[f21])).
% 2.16/0.67  fof(f21,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 2.16/0.67  fof(f3003,plain,(
% 2.16/0.67    ~r1_tarski(k7_relat_1(sK2,sK3),k2_zfmisc_1(sK3,u1_struct_0(sK1))) | spl6_5),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f201,f95])).
% 2.16/0.67  fof(f95,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f8])).
% 2.16/0.67  fof(f201,plain,(
% 2.16/0.67    ~m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) | spl6_5),
% 2.16/0.67    inference(avatar_component_clause,[],[f199])).
% 2.16/0.67  fof(f199,plain,(
% 2.16/0.67    spl6_5 <=> m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.16/0.67  fof(f2151,plain,(
% 2.16/0.67    ~spl6_1 | spl6_4 | ~spl6_12),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f2144])).
% 2.16/0.67  fof(f2144,plain,(
% 2.16/0.67    $false | (~spl6_1 | spl6_4 | ~spl6_12)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f145,f1261,f2100,f100])).
% 2.16/0.67  fof(f100,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f54])).
% 2.16/0.67  fof(f54,plain,(
% 2.16/0.67    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(flattening,[],[f53])).
% 2.16/0.67  fof(f53,plain,(
% 2.16/0.67    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(ennf_transformation,[],[f13])).
% 2.16/0.67  fof(f13,axiom,(
% 2.16/0.67    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.16/0.67  fof(f2100,plain,(
% 2.16/0.67    sK3 != k1_relat_1(k7_relat_1(sK2,sK3)) | (~spl6_1 | spl6_4)),
% 2.16/0.67    inference(superposition,[],[f274,f275])).
% 2.16/0.67  fof(f275,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK2,X0))) )),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f158,f85])).
% 2.16/0.67  fof(f85,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f48])).
% 2.16/0.67  fof(f48,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f19])).
% 2.16/0.67  fof(f19,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.16/0.67  fof(f274,plain,(
% 2.16/0.67    sK3 != k1_relset_1(sK3,u1_struct_0(sK1),k7_relat_1(sK2,sK3)) | (~spl6_1 | spl6_4)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f135,f197,f158,f69])).
% 2.16/0.67  fof(f69,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f37])).
% 2.16/0.67  fof(f37,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.16/0.67    inference(flattening,[],[f36])).
% 2.16/0.67  fof(f36,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.16/0.67    inference(ennf_transformation,[],[f26])).
% 2.16/0.67  fof(f26,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 2.16/0.67  fof(f197,plain,(
% 2.16/0.67    ~v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) | spl6_4),
% 2.16/0.67    inference(avatar_component_clause,[],[f195])).
% 2.16/0.67  fof(f195,plain,(
% 2.16/0.67    spl6_4 <=> v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.16/0.67  fof(f135,plain,(
% 2.16/0.67    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) ) | ~spl6_1),
% 2.16/0.67    inference(avatar_component_clause,[],[f134])).
% 2.16/0.67  fof(f134,plain,(
% 2.16/0.67    spl6_1 <=> ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.16/0.67  fof(f1261,plain,(
% 2.16/0.67    r1_tarski(sK3,k1_relat_1(sK2)) | ~spl6_12),
% 2.16/0.67    inference(backward_demodulation,[],[f119,f444])).
% 2.16/0.67  fof(f444,plain,(
% 2.16/0.67    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl6_12),
% 2.16/0.67    inference(avatar_component_clause,[],[f442])).
% 2.16/0.67  fof(f442,plain,(
% 2.16/0.67    spl6_12 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.16/0.67  fof(f119,plain,(
% 2.16/0.67    r1_tarski(sK3,u1_struct_0(sK0))),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f58,f96])).
% 2.16/0.67  fof(f58,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f145,plain,(
% 2.16/0.67    v1_relat_1(sK2)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f61,f68])).
% 2.16/0.67  fof(f68,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f35])).
% 2.16/0.67  fof(f35,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f17])).
% 2.16/0.67  fof(f17,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.16/0.67  fof(f1093,plain,(
% 2.16/0.67    ~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_11),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f1080])).
% 2.16/0.67  fof(f1080,plain,(
% 2.16/0.67    $false | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f1059,f1051])).
% 2.16/0.67  fof(f1051,plain,(
% 2.16/0.67    k1_xboole_0 != sK3 | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(forward_demodulation,[],[f951,f1048])).
% 2.16/0.67  fof(f1048,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 = k1_relset_1(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f925,f950])).
% 2.16/0.67  fof(f950,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_8),
% 2.16/0.67    inference(backward_demodulation,[],[f849,f883])).
% 2.16/0.67  fof(f883,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f642,f774,f90])).
% 2.16/0.67  fof(f90,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f49])).
% 2.16/0.67  fof(f49,plain,(
% 2.16/0.67    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f4])).
% 2.16/0.67  fof(f4,axiom,(
% 2.16/0.67    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.16/0.67  fof(f774,plain,(
% 2.16/0.67    ( ! [X0] : (v1_xboole_0(k7_relat_1(k1_xboole_0,X0))) ) | ~spl6_8),
% 2.16/0.67    inference(backward_demodulation,[],[f643,f659])).
% 2.16/0.67  fof(f659,plain,(
% 2.16/0.67    k1_xboole_0 = sK2 | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f390,f642,f90])).
% 2.16/0.67  fof(f390,plain,(
% 2.16/0.67    v1_xboole_0(sK2) | ~spl6_8),
% 2.16/0.67    inference(avatar_component_clause,[],[f389])).
% 2.16/0.67  fof(f389,plain,(
% 2.16/0.67    spl6_8 <=> v1_xboole_0(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.16/0.67  fof(f643,plain,(
% 2.16/0.67    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK2,X0))) ) | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f180,f390,f93])).
% 2.16/0.67  fof(f93,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f50])).
% 2.16/0.67  fof(f50,plain,(
% 2.16/0.67    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f7])).
% 2.16/0.67  fof(f7,axiom,(
% 2.16/0.67    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.16/0.67  fof(f180,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(sK2))) )),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f161,f95])).
% 2.16/0.67  fof(f161,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) )),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f145,f84])).
% 2.16/0.67  fof(f84,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f47])).
% 2.16/0.67  fof(f47,plain,(
% 2.16/0.67    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.16/0.67    inference(ennf_transformation,[],[f12])).
% 2.16/0.67  fof(f12,axiom,(
% 2.16/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.16/0.67  fof(f642,plain,(
% 2.16/0.67    v1_xboole_0(k1_xboole_0) | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f89,f390,f93])).
% 2.16/0.67  fof(f89,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f6])).
% 2.16/0.67  fof(f6,axiom,(
% 2.16/0.67    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.16/0.67  fof(f849,plain,(
% 2.16/0.67    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f669,f825,f100])).
% 2.16/0.67  fof(f825,plain,(
% 2.16/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f775,f98])).
% 2.16/0.67  fof(f98,plain,(
% 2.16/0.67    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f52])).
% 2.16/0.67  fof(f52,plain,(
% 2.16/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.16/0.67    inference(ennf_transformation,[],[f2])).
% 2.16/0.67  fof(f2,axiom,(
% 2.16/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.16/0.67  fof(f775,plain,(
% 2.16/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_8),
% 2.16/0.67    inference(backward_demodulation,[],[f644,f659])).
% 2.16/0.67  fof(f644,plain,(
% 2.16/0.67    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f390,f92])).
% 2.16/0.67  fof(f92,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f1])).
% 2.16/0.67  fof(f1,axiom,(
% 2.16/0.67    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.16/0.67  fof(f669,plain,(
% 2.16/0.67    v1_relat_1(k1_xboole_0) | ~spl6_8),
% 2.16/0.67    inference(backward_demodulation,[],[f145,f659])).
% 2.16/0.67  fof(f925,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f747,f883])).
% 2.16/0.67  fof(f747,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k1_relset_1(X0,k1_xboole_0,k7_relat_1(k1_xboole_0,X0))) ) | (~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f473,f659])).
% 2.16/0.67  fof(f473,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_relset_1(X0,k1_xboole_0,k7_relat_1(sK2,X0))) ) | ~spl6_11),
% 2.16/0.67    inference(backward_demodulation,[],[f275,f440])).
% 2.16/0.67  fof(f440,plain,(
% 2.16/0.67    k1_xboole_0 = u1_struct_0(sK1) | ~spl6_11),
% 2.16/0.67    inference(avatar_component_clause,[],[f438])).
% 2.16/0.67  fof(f438,plain,(
% 2.16/0.67    spl6_11 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.16/0.67  fof(f951,plain,(
% 2.16/0.67    sK3 != k1_relset_1(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f746,f883])).
% 2.16/0.67  fof(f746,plain,(
% 2.16/0.67    sK3 != k1_relset_1(sK3,k1_xboole_0,k7_relat_1(k1_xboole_0,sK3)) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f472,f659])).
% 2.16/0.67  fof(f472,plain,(
% 2.16/0.67    sK3 != k1_relset_1(sK3,k1_xboole_0,k7_relat_1(sK2,sK3)) | (~spl6_1 | spl6_4 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f274,f440])).
% 2.16/0.67  fof(f1059,plain,(
% 2.16/0.67    k1_xboole_0 = sK3 | (spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f89,f952,f106])).
% 2.16/0.67  fof(f106,plain,(
% 2.16/0.67    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 2.16/0.67    inference(equality_resolution,[],[f105])).
% 2.16/0.67  fof(f105,plain,(
% 2.16/0.67    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 2.16/0.67    inference(equality_resolution,[],[f70])).
% 2.16/0.67  fof(f70,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f39])).
% 2.16/0.67  fof(f39,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(flattening,[],[f38])).
% 2.16/0.67  fof(f38,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(ennf_transformation,[],[f23])).
% 2.16/0.67  fof(f23,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.16/0.67  fof(f952,plain,(
% 2.16/0.67    ~v1_funct_2(k1_xboole_0,sK3,k1_xboole_0) | (spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f744,f883])).
% 2.16/0.67  fof(f744,plain,(
% 2.16/0.67    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK3),sK3,k1_xboole_0) | (spl6_4 | ~spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f462,f659])).
% 2.16/0.67  fof(f462,plain,(
% 2.16/0.67    ~v1_funct_2(k7_relat_1(sK2,sK3),sK3,k1_xboole_0) | (spl6_4 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f197,f440])).
% 2.16/0.67  fof(f640,plain,(
% 2.16/0.67    spl6_8 | ~spl6_11),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f639])).
% 2.16/0.67  fof(f639,plain,(
% 2.16/0.67    $false | (spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f89,f568,f96])).
% 2.16/0.67  fof(f568,plain,(
% 2.16/0.67    ~r1_tarski(k1_xboole_0,sK4(sK2)) | (spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f524,f94])).
% 2.16/0.67  fof(f94,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f51])).
% 2.16/0.67  fof(f51,plain,(
% 2.16/0.67    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.16/0.67    inference(ennf_transformation,[],[f16])).
% 2.16/0.67  fof(f16,axiom,(
% 2.16/0.67    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.16/0.67  fof(f524,plain,(
% 2.16/0.67    r2_hidden(sK4(sK2),k1_xboole_0) | (spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(forward_demodulation,[],[f489,f109])).
% 2.16/0.67  fof(f109,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.16/0.67    inference(equality_resolution,[],[f88])).
% 2.16/0.67  fof(f88,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f5])).
% 2.16/0.67  fof(f5,axiom,(
% 2.16/0.67    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.16/0.67  fof(f489,plain,(
% 2.16/0.67    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | (spl6_8 | ~spl6_11)),
% 2.16/0.67    inference(backward_demodulation,[],[f400,f440])).
% 2.16/0.67  fof(f400,plain,(
% 2.16/0.67    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f148,f397,f97])).
% 2.16/0.67  fof(f97,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f52])).
% 2.16/0.67  fof(f397,plain,(
% 2.16/0.67    r2_hidden(sK4(sK2),sK2) | spl6_8),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f391,f91])).
% 2.16/0.67  fof(f91,plain,(
% 2.16/0.67    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f1])).
% 2.16/0.67  fof(f391,plain,(
% 2.16/0.67    ~v1_xboole_0(sK2) | spl6_8),
% 2.16/0.67    inference(avatar_component_clause,[],[f389])).
% 2.16/0.67  fof(f148,plain,(
% 2.16/0.67    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f61,f96])).
% 2.16/0.67  fof(f453,plain,(
% 2.16/0.67    spl6_10),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f448])).
% 2.16/0.67  fof(f448,plain,(
% 2.16/0.67    $false | spl6_10),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f148,f436,f95])).
% 2.16/0.67  fof(f436,plain,(
% 2.16/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl6_10),
% 2.16/0.67    inference(avatar_component_clause,[],[f434])).
% 2.16/0.67  fof(f434,plain,(
% 2.16/0.67    spl6_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.16/0.67  fof(f445,plain,(
% 2.16/0.67    ~spl6_10 | spl6_11 | spl6_12),
% 2.16/0.67    inference(avatar_split_clause,[],[f154,f442,f438,f434])).
% 2.16/0.67  fof(f154,plain,(
% 2.16/0.67    u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.16/0.67    inference(backward_demodulation,[],[f132,f147])).
% 2.16/0.67  fof(f147,plain,(
% 2.16/0.67    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f61,f85])).
% 2.16/0.67  fof(f132,plain,(
% 2.16/0.67    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.16/0.67    inference(resolution,[],[f60,f75])).
% 2.16/0.67  fof(f75,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f39])).
% 2.16/0.67  fof(f60,plain,(
% 2.16/0.67    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f211,plain,(
% 2.16/0.67    spl6_3),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f206])).
% 2.16/0.67  fof(f206,plain,(
% 2.16/0.67    $false | spl6_3),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f59,f145,f193,f78])).
% 2.16/0.67  fof(f78,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k7_relat_1(X0,X1))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f43])).
% 2.16/0.67  fof(f43,plain,(
% 2.16/0.67    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(flattening,[],[f42])).
% 2.16/0.67  fof(f42,plain,(
% 2.16/0.67    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/0.67    inference(ennf_transformation,[],[f15])).
% 2.16/0.67  fof(f15,axiom,(
% 2.16/0.67    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.16/0.67  fof(f193,plain,(
% 2.16/0.67    ~v1_funct_1(k7_relat_1(sK2,sK3)) | spl6_3),
% 2.16/0.67    inference(avatar_component_clause,[],[f191])).
% 2.16/0.67  fof(f191,plain,(
% 2.16/0.67    spl6_3 <=> v1_funct_1(k7_relat_1(sK2,sK3))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.16/0.67  fof(f59,plain,(
% 2.16/0.67    v1_funct_1(sK2)),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f202,plain,(
% 2.16/0.67    ~spl6_3 | ~spl6_4 | ~spl6_5),
% 2.16/0.67    inference(avatar_split_clause,[],[f157,f199,f195,f191])).
% 2.16/0.67  fof(f157,plain,(
% 2.16/0.67    ~m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) | ~v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,sK3))),
% 2.16/0.67    inference(forward_demodulation,[],[f156,f144])).
% 2.16/0.67  fof(f156,plain,(
% 2.16/0.67    ~v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,sK3)) | ~m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))),
% 2.16/0.67    inference(forward_demodulation,[],[f155,f144])).
% 2.16/0.67  fof(f155,plain,(
% 2.16/0.67    ~v1_funct_1(k7_relat_1(sK2,sK3)) | ~v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1)) | ~m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))),
% 2.16/0.67    inference(backward_demodulation,[],[f123,f144])).
% 2.16/0.67  fof(f123,plain,(
% 2.16/0.67    ~v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1)) | ~m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) | ~v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))),
% 2.16/0.67    inference(forward_demodulation,[],[f122,f118])).
% 2.16/0.67  fof(f118,plain,(
% 2.16/0.67    sK3 = u1_struct_0(k1_pre_topc(sK0,sK3))),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f64,f58,f65])).
% 2.16/0.67  fof(f65,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 2.16/0.67    inference(cnf_transformation,[],[f32])).
% 2.16/0.67  fof(f32,plain,(
% 2.16/0.67    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f27])).
% 2.16/0.67  fof(f27,axiom,(
% 2.16/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 2.16/0.67  fof(f64,plain,(
% 2.16/0.67    l1_pre_topc(sK0)),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f122,plain,(
% 2.16/0.67    ~m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) | ~v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))),
% 2.16/0.67    inference(backward_demodulation,[],[f57,f118])).
% 2.16/0.67  fof(f57,plain,(
% 2.16/0.67    ~v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)) | ~m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f153,plain,(
% 2.16/0.67    spl6_2),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f146])).
% 2.16/0.67  fof(f146,plain,(
% 2.16/0.67    $false | spl6_2),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f139,f61,f68])).
% 2.16/0.67  fof(f139,plain,(
% 2.16/0.67    ~v1_relat_1(sK2) | spl6_2),
% 2.16/0.67    inference(avatar_component_clause,[],[f137])).
% 2.16/0.67  fof(f137,plain,(
% 2.16/0.67    spl6_2 <=> v1_relat_1(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.16/0.67  fof(f140,plain,(
% 2.16/0.67    spl6_1 | ~spl6_2),
% 2.16/0.67    inference(avatar_split_clause,[],[f111,f137,f134])).
% 2.16/0.67  fof(f111,plain,(
% 2.16/0.67    ( ! [X0] : (~v1_relat_1(sK2) | v1_funct_1(k7_relat_1(sK2,X0))) )),
% 2.16/0.67    inference(resolution,[],[f59,f78])).
% 2.16/0.67  % SZS output end Proof for theBenchmark
% 2.16/0.67  % (32746)------------------------------
% 2.16/0.67  % (32746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (32746)Termination reason: Refutation
% 2.16/0.67  
% 2.16/0.67  % (32746)Memory used [KB]: 7291
% 2.16/0.67  % (32746)Time elapsed: 0.230 s
% 2.16/0.67  % (32746)------------------------------
% 2.16/0.67  % (32746)------------------------------
% 2.16/0.67  % (32741)Success in time 0.307 s
%------------------------------------------------------------------------------
