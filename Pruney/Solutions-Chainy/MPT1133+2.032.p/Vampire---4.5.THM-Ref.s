%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:35 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  237 (1149 expanded)
%              Number of leaves         :   33 ( 272 expanded)
%              Depth                    :   18
%              Number of atoms          :  911 (8750 expanded)
%              Number of equality atoms :   97 ( 824 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8692,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f419,f784,f1098,f1131,f1286,f1322,f1761,f2112,f2980,f3922,f3933,f4585,f4656,f5062,f6827,f8411,f8561,f8562,f8672,f8691])).

fof(f8691,plain,
    ( ~ spl4_4
    | spl4_72
    | ~ spl4_89 ),
    inference(avatar_contradiction_clause,[],[f8687])).

fof(f8687,plain,
    ( $false
    | ~ spl4_4
    | spl4_72
    | ~ spl4_89 ),
    inference(subsumption_resolution,[],[f5256,f8582])).

fof(f8582,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | spl4_72
    | ~ spl4_89 ),
    inference(backward_demodulation,[],[f6831,f8410])).

fof(f8410,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f8408])).

fof(f8408,plain,
    ( spl4_89
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f6831,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | spl4_72 ),
    inference(resolution,[],[f6822,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f6822,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f6820])).

fof(f6820,plain,
    ( spl4_72
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f5256,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | ~ spl4_4 ),
    inference(resolution,[],[f5196,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f5196,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f44,f418])).

fof(f418,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl4_4
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f8672,plain,
    ( ~ spl4_4
    | spl4_73
    | ~ spl4_89 ),
    inference(avatar_contradiction_clause,[],[f8666])).

fof(f8666,plain,
    ( $false
    | ~ spl4_4
    | spl4_73
    | ~ spl4_89 ),
    inference(subsumption_resolution,[],[f5195,f8581])).

fof(f8581,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | spl4_73
    | ~ spl4_89 ),
    inference(backward_demodulation,[],[f6826,f8410])).

fof(f6826,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl4_73 ),
    inference(avatar_component_clause,[],[f6824])).

fof(f6824,plain,
    ( spl4_73
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f5195,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f43,f418])).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f8562,plain,
    ( spl4_87
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f5297,f416,f8400])).

fof(f8400,plain,
    ( spl4_87
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f5297,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f253,f418])).

fof(f253,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f39,f41])).

fof(f41,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f8561,plain,
    ( ~ spl4_4
    | spl4_13
    | ~ spl4_88 ),
    inference(avatar_contradiction_clause,[],[f8559])).

fof(f8559,plain,
    ( $false
    | ~ spl4_4
    | spl4_13
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1285,f8480])).

fof(f8480,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f8426,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f8426,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_88 ),
    inference(backward_demodulation,[],[f5403,f8406])).

fof(f8406,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f8404])).

fof(f8404,plain,
    ( spl4_88
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f5403,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl4_4 ),
    inference(resolution,[],[f5344,f65])).

fof(f5344,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f410,f418])).

fof(f410,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f19])).

fof(f1285,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f1283])).

fof(f1283,plain,
    ( spl4_13
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f8411,plain,
    ( ~ spl4_87
    | spl4_88
    | spl4_89
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f8334,f416,f8408,f8404,f8400])).

fof(f8334,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f5401,f5398])).

fof(f5398,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f5344,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f5401,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_4 ),
    inference(resolution,[],[f5344,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f6827,plain,
    ( ~ spl4_72
    | ~ spl4_73
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f6229,f416,f6824,f6820])).

fof(f6229,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f6228,f418])).

fof(f6228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f568,f418])).

fof(f568,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f220,f221,f293,f294,f335,f374,f410])).

fof(f374,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f37,f41])).

fof(f37,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f335,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f36,f41])).

fof(f36,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f294,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f42,f45,f46,f151,f255,f285])).

fof(f285,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(resolution,[],[f253,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f255,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f160,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f160,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(global_subsumption,[],[f48,f142])).

fof(f142,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f293,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(global_subsumption,[],[f42,f45,f46,f151,f255,f284])).

fof(f284,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(resolution,[],[f253,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f221,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f186])).

fof(f186,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f181])).

fof(f181,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f43,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f220,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f185])).

fof(f185,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f180])).

fof(f180,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f43,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5062,plain,
    ( ~ spl4_32
    | ~ spl4_46
    | spl4_57 ),
    inference(avatar_contradiction_clause,[],[f5042])).

fof(f5042,plain,
    ( $false
    | ~ spl4_32
    | ~ spl4_46
    | spl4_57 ),
    inference(resolution,[],[f4915,f2979])).

fof(f2979,plain,
    ( ! [X6] : v1_funct_2(k1_xboole_0,k1_xboole_0,X6)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f2978])).

fof(f2978,plain,
    ( spl4_32
  <=> ! [X6] : v1_funct_2(k1_xboole_0,k1_xboole_0,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f4915,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_46
    | spl4_57 ),
    inference(backward_demodulation,[],[f4584,f4718])).

fof(f4718,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_46
    | spl4_57 ),
    inference(resolution,[],[f3622,f4584])).

fof(f3622,plain,
    ( ! [X19] :
        ( v1_funct_2(k1_xboole_0,X19,k1_xboole_0)
        | k1_xboole_0 = X19 )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f3621])).

fof(f3621,plain,
    ( spl4_46
  <=> ! [X19] :
        ( k1_xboole_0 = X19
        | v1_funct_2(k1_xboole_0,X19,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f4584,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl4_57 ),
    inference(avatar_component_clause,[],[f4582])).

fof(f4582,plain,
    ( spl4_57
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f4656,plain,
    ( spl4_46
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f4597,f771,f3621])).

fof(f771,plain,
    ( spl4_8
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f4597,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f92,f86])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4585,plain,
    ( ~ spl4_57
    | ~ spl4_8
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f4580,f1091,f412,f771,f4582])).

fof(f412,plain,
    ( spl4_3
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1091,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f4580,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f4579,f1093])).

fof(f1093,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f4579,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f4578,f86])).

fof(f4578,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f4577,f414])).

fof(f414,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f412])).

fof(f4577,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f4576,f1093])).

fof(f4576,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f845,f414])).

fof(f845,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(global_subsumption,[],[f569])).

fof(f569,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(global_subsumption,[],[f568])).

fof(f3933,plain,
    ( ~ spl4_32
    | spl4_52 ),
    inference(avatar_contradiction_clause,[],[f3923])).

fof(f3923,plain,
    ( $false
    | ~ spl4_32
    | spl4_52 ),
    inference(resolution,[],[f3921,f2979])).

fof(f3921,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f3919])).

fof(f3919,plain,
    ( spl4_52
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f3922,plain,
    ( ~ spl4_8
    | ~ spl4_52
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f3917,f1319,f1091,f416,f3919,f771])).

fof(f1319,plain,
    ( spl4_15
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f3917,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f3916,f1093])).

fof(f3916,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f3915,f2150])).

fof(f2150,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f418,f1321])).

fof(f1321,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f3915,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f3914,f1093])).

fof(f3914,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f3913,f87])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3913,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f570,f2150])).

fof(f570,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(global_subsumption,[],[f222,f223,f291,f292,f335,f374,f410])).

fof(f292,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(global_subsumption,[],[f42,f47,f48,f114,f208,f283])).

fof(f283,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f253,f95])).

fof(f208,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f123,f60])).

fof(f123,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f46,f50])).

fof(f114,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_subsumption,[],[f46,f105])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f45,f52])).

fof(f291,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(global_subsumption,[],[f42,f47,f48,f114,f208,f282])).

fof(f282,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f253,f96])).

fof(f223,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f188])).

fof(f188,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f183])).

fof(f183,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f43,f93])).

fof(f222,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(global_subsumption,[],[f187])).

fof(f187,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f182])).

fof(f182,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f43,f94])).

fof(f2980,plain,
    ( spl4_32
    | ~ spl4_8
    | ~ spl4_22
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f2976,f1319,f1091,f2020,f771,f2978])).

fof(f2020,plain,
    ( spl4_22
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f2976,plain,
    ( ! [X6] :
        ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X6) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f2975,f87])).

fof(f2975,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X6)
        | ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X6)) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f2971,f87])).

fof(f2971,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X6)
        | ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X6)) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f2970])).

fof(f2970,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X6)
        | ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X6)) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(superposition,[],[f89,f2956])).

fof(f2956,plain,
    ( ! [X23,X22] :
        ( k1_xboole_0 = k1_relset_1(X22,X23,k1_xboole_0)
        | ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23)) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f2955,f1766])).

fof(f1766,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f1321,f1093])).

fof(f2955,plain,
    ( ! [X23,X22] :
        ( k1_relat_1(k1_xboole_0) = k1_relset_1(X22,X23,k1_xboole_0)
        | ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23)) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f2954,f1766])).

fof(f2954,plain,
    ( ! [X23,X22] :
        ( k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relset_1(X22,X23,k1_relat_1(k1_xboole_0))
        | ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23)) )
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f2953,f1093])).

fof(f2953,plain,
    ( ! [X23,X22] :
        ( ~ v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23))
        | k1_relset_1(X22,X23,k1_relat_1(sK2)) = k1_relat_1(k1_relat_1(sK2)) )
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f313,f1093])).

fof(f313,plain,(
    ! [X23,X22] :
      ( k1_relset_1(X22,X23,k1_relat_1(sK2)) = k1_relat_1(k1_relat_1(sK2))
      | ~ v4_relat_1(sK2,k2_zfmisc_1(X22,X23)) ) ),
    inference(resolution,[],[f299,f70])).

fof(f299,plain,(
    ! [X0] :
      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f225,f64])).

fof(f225,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f218,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f218,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f44,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2112,plain,
    ( ~ spl4_8
    | spl4_22 ),
    inference(avatar_split_clause,[],[f2038,f2020,f771])).

fof(f2038,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_22 ),
    inference(forward_demodulation,[],[f2029,f87])).

fof(f2029,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | spl4_22 ),
    inference(resolution,[],[f2022,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2022,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f2020])).

fof(f1761,plain,
    ( ~ spl4_8
    | ~ spl4_11
    | spl4_14 ),
    inference(avatar_split_clause,[],[f1671,f1315,f1091,f771])).

fof(f1315,plain,
    ( spl4_14
  <=> v4_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1671,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_11
    | spl4_14 ),
    inference(forward_demodulation,[],[f1663,f87])).

fof(f1663,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl4_11
    | spl4_14 ),
    inference(resolution,[],[f1573,f71])).

fof(f1573,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_11
    | spl4_14 ),
    inference(backward_demodulation,[],[f1317,f1093])).

fof(f1317,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1322,plain,
    ( ~ spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f756,f1319,f1315])).

fof(f756,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f734,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f734,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK2)))
      | k1_relat_1(sK2) = X0
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f300,f65])).

fof(f300,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK2))
      | ~ v4_relat_1(sK2,X1)
      | k1_relat_1(sK2) = X1 ) ),
    inference(resolution,[],[f225,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1286,plain,
    ( spl4_11
    | ~ spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f1138,f1095,f1283,f1091])).

fof(f1095,plain,
    ( spl4_12
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1138,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_12 ),
    inference(resolution,[],[f1096,f63])).

fof(f1096,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f1095])).

fof(f1131,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f1122])).

fof(f1122,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f1099,f49])).

fof(f1099,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | spl4_12 ),
    inference(resolution,[],[f1097,f65])).

fof(f1097,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f1095])).

fof(f1098,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f814,f412,f1095,f1091])).

fof(f814,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(resolution,[],[f468,f63])).

fof(f468,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f427,f86])).

fof(f427,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f219,f414])).

fof(f219,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f44,f65])).

fof(f784,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f775])).

fof(f775,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f773,f49])).

fof(f773,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f771])).

fof(f419,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f408,f416,f412])).

fof(f408,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_subsumption,[],[f43,f44,f405])).

fof(f405,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(superposition,[],[f217,f78])).

fof(f217,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f44,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:36:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (14972)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.46  % (14963)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (14963)Refutation not found, incomplete strategy% (14963)------------------------------
% 0.21/0.47  % (14963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14963)Memory used [KB]: 10874
% 0.21/0.48  % (14963)Time elapsed: 0.061 s
% 0.21/0.48  % (14963)------------------------------
% 0.21/0.48  % (14963)------------------------------
% 0.21/0.50  % (14954)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (14953)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14952)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14965)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14952)Refutation not found, incomplete strategy% (14952)------------------------------
% 0.21/0.51  % (14952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14952)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14952)Memory used [KB]: 10618
% 0.21/0.51  % (14952)Time elapsed: 0.098 s
% 0.21/0.51  % (14952)------------------------------
% 0.21/0.51  % (14952)------------------------------
% 0.21/0.51  % (14965)Refutation not found, incomplete strategy% (14965)------------------------------
% 0.21/0.51  % (14965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14965)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14965)Memory used [KB]: 6268
% 0.21/0.51  % (14965)Time elapsed: 0.096 s
% 0.21/0.51  % (14965)------------------------------
% 0.21/0.51  % (14965)------------------------------
% 0.21/0.51  % (14971)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (14958)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (14955)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (14961)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (14958)Refutation not found, incomplete strategy% (14958)------------------------------
% 0.21/0.51  % (14958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14958)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14958)Memory used [KB]: 10618
% 0.21/0.51  % (14958)Time elapsed: 0.104 s
% 0.21/0.51  % (14958)------------------------------
% 0.21/0.51  % (14958)------------------------------
% 0.21/0.51  % (14976)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (14966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (14970)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (14960)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (14975)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (14969)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (14964)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (14967)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (14968)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (14974)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (14959)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (14973)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (14957)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (14962)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (14977)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.58  % (14953)Refutation not found, incomplete strategy% (14953)------------------------------
% 0.21/0.58  % (14953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (14953)Memory used [KB]: 11513
% 0.21/0.58  % (14953)Time elapsed: 0.160 s
% 0.21/0.58  % (14953)------------------------------
% 0.21/0.58  % (14953)------------------------------
% 2.16/0.68  % (14961)Refutation not found, incomplete strategy% (14961)------------------------------
% 2.16/0.68  % (14961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (14961)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (14961)Memory used [KB]: 6268
% 2.16/0.68  % (14961)Time elapsed: 0.269 s
% 2.16/0.68  % (14961)------------------------------
% 2.16/0.68  % (14961)------------------------------
% 2.76/0.77  % (14972)Refutation found. Thanks to Tanya!
% 2.76/0.77  % SZS status Theorem for theBenchmark
% 2.76/0.77  % SZS output start Proof for theBenchmark
% 2.76/0.77  fof(f8692,plain,(
% 2.76/0.77    $false),
% 2.76/0.77    inference(avatar_sat_refutation,[],[f419,f784,f1098,f1131,f1286,f1322,f1761,f2112,f2980,f3922,f3933,f4585,f4656,f5062,f6827,f8411,f8561,f8562,f8672,f8691])).
% 2.76/0.77  fof(f8691,plain,(
% 2.76/0.77    ~spl4_4 | spl4_72 | ~spl4_89),
% 2.76/0.77    inference(avatar_contradiction_clause,[],[f8687])).
% 2.76/0.77  fof(f8687,plain,(
% 2.76/0.77    $false | (~spl4_4 | spl4_72 | ~spl4_89)),
% 2.76/0.77    inference(subsumption_resolution,[],[f5256,f8582])).
% 2.76/0.77  fof(f8582,plain,(
% 2.76/0.77    ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | (spl4_72 | ~spl4_89)),
% 2.76/0.77    inference(backward_demodulation,[],[f6831,f8410])).
% 2.76/0.77  fof(f8410,plain,(
% 2.76/0.77    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl4_89),
% 2.76/0.77    inference(avatar_component_clause,[],[f8408])).
% 2.76/0.77  fof(f8408,plain,(
% 2.76/0.77    spl4_89 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 2.76/0.77  fof(f6831,plain,(
% 2.76/0.77    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))) | spl4_72),
% 2.76/0.77    inference(resolution,[],[f6822,f64])).
% 2.76/0.77  fof(f64,plain,(
% 2.76/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.76/0.77    inference(cnf_transformation,[],[f4])).
% 2.76/0.77  fof(f4,axiom,(
% 2.76/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.76/0.77  fof(f6822,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl4_72),
% 2.76/0.77    inference(avatar_component_clause,[],[f6820])).
% 2.76/0.77  fof(f6820,plain,(
% 2.76/0.77    spl4_72 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 2.76/0.77  fof(f5256,plain,(
% 2.76/0.77    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | ~spl4_4),
% 2.76/0.77    inference(resolution,[],[f5196,f65])).
% 2.76/0.77  fof(f65,plain,(
% 2.76/0.77    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.76/0.77    inference(cnf_transformation,[],[f4])).
% 2.76/0.77  fof(f5196,plain,(
% 2.76/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl4_4),
% 2.76/0.77    inference(backward_demodulation,[],[f44,f418])).
% 2.76/0.77  fof(f418,plain,(
% 2.76/0.77    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_4),
% 2.76/0.77    inference(avatar_component_clause,[],[f416])).
% 2.76/0.77  fof(f416,plain,(
% 2.76/0.77    spl4_4 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.76/0.77  fof(f44,plain,(
% 2.76/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f19,plain,(
% 2.76/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.76/0.77    inference(flattening,[],[f18])).
% 2.76/0.77  fof(f18,plain,(
% 2.76/0.77    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.76/0.77    inference(ennf_transformation,[],[f17])).
% 2.76/0.77  fof(f17,negated_conjecture,(
% 2.76/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.76/0.77    inference(negated_conjecture,[],[f16])).
% 2.76/0.77  fof(f16,conjecture,(
% 2.76/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 2.76/0.77  fof(f8672,plain,(
% 2.76/0.77    ~spl4_4 | spl4_73 | ~spl4_89),
% 2.76/0.77    inference(avatar_contradiction_clause,[],[f8666])).
% 2.76/0.77  fof(f8666,plain,(
% 2.76/0.77    $false | (~spl4_4 | spl4_73 | ~spl4_89)),
% 2.76/0.77    inference(subsumption_resolution,[],[f5195,f8581])).
% 2.76/0.77  fof(f8581,plain,(
% 2.76/0.77    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (spl4_73 | ~spl4_89)),
% 2.76/0.77    inference(backward_demodulation,[],[f6826,f8410])).
% 2.76/0.77  fof(f6826,plain,(
% 2.76/0.77    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl4_73),
% 2.76/0.77    inference(avatar_component_clause,[],[f6824])).
% 2.76/0.77  fof(f6824,plain,(
% 2.76/0.77    spl4_73 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 2.76/0.77  fof(f5195,plain,(
% 2.76/0.77    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl4_4),
% 2.76/0.77    inference(backward_demodulation,[],[f43,f418])).
% 2.76/0.77  fof(f43,plain,(
% 2.76/0.77    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f8562,plain,(
% 2.76/0.77    spl4_87 | ~spl4_4),
% 2.76/0.77    inference(avatar_split_clause,[],[f5297,f416,f8400])).
% 2.76/0.77  fof(f8400,plain,(
% 2.76/0.77    spl4_87 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 2.76/0.77  fof(f5297,plain,(
% 2.76/0.77    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_4),
% 2.76/0.77    inference(forward_demodulation,[],[f253,f418])).
% 2.76/0.77  fof(f253,plain,(
% 2.76/0.77    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.76/0.77    inference(forward_demodulation,[],[f39,f41])).
% 2.76/0.77  fof(f41,plain,(
% 2.76/0.77    sK2 = sK3),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f39,plain,(
% 2.76/0.77    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f8561,plain,(
% 2.76/0.77    ~spl4_4 | spl4_13 | ~spl4_88),
% 2.76/0.77    inference(avatar_contradiction_clause,[],[f8559])).
% 2.76/0.77  fof(f8559,plain,(
% 2.76/0.77    $false | (~spl4_4 | spl4_13 | ~spl4_88)),
% 2.76/0.77    inference(subsumption_resolution,[],[f1285,f8480])).
% 2.76/0.77  fof(f8480,plain,(
% 2.76/0.77    r1_tarski(sK2,k1_xboole_0) | (~spl4_4 | ~spl4_88)),
% 2.76/0.77    inference(forward_demodulation,[],[f8426,f86])).
% 2.76/0.77  fof(f86,plain,(
% 2.76/0.77    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.76/0.77    inference(equality_resolution,[],[f68])).
% 2.76/0.77  fof(f68,plain,(
% 2.76/0.77    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 2.76/0.77    inference(cnf_transformation,[],[f2])).
% 2.76/0.77  fof(f2,axiom,(
% 2.76/0.77    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.76/0.77  fof(f8426,plain,(
% 2.76/0.77    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)) | (~spl4_4 | ~spl4_88)),
% 2.76/0.77    inference(backward_demodulation,[],[f5403,f8406])).
% 2.76/0.77  fof(f8406,plain,(
% 2.76/0.77    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_88),
% 2.76/0.77    inference(avatar_component_clause,[],[f8404])).
% 2.76/0.77  fof(f8404,plain,(
% 2.76/0.77    spl4_88 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 2.76/0.77  fof(f5403,plain,(
% 2.76/0.77    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl4_4),
% 2.76/0.77    inference(resolution,[],[f5344,f65])).
% 2.76/0.77  fof(f5344,plain,(
% 2.76/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_4),
% 2.76/0.77    inference(forward_demodulation,[],[f410,f418])).
% 2.76/0.77  fof(f410,plain,(
% 2.76/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.76/0.77    inference(forward_demodulation,[],[f40,f41])).
% 2.76/0.77  fof(f40,plain,(
% 2.76/0.77    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f1285,plain,(
% 2.76/0.77    ~r1_tarski(sK2,k1_xboole_0) | spl4_13),
% 2.76/0.77    inference(avatar_component_clause,[],[f1283])).
% 2.76/0.77  fof(f1283,plain,(
% 2.76/0.77    spl4_13 <=> r1_tarski(sK2,k1_xboole_0)),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.76/0.77  fof(f8411,plain,(
% 2.76/0.77    ~spl4_87 | spl4_88 | spl4_89 | ~spl4_4),
% 2.76/0.77    inference(avatar_split_clause,[],[f8334,f416,f8408,f8404,f8400])).
% 2.76/0.77  fof(f8334,plain,(
% 2.76/0.77    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_4),
% 2.76/0.77    inference(forward_demodulation,[],[f5401,f5398])).
% 2.76/0.77  fof(f5398,plain,(
% 2.76/0.77    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl4_4),
% 2.76/0.77    inference(resolution,[],[f5344,f70])).
% 2.76/0.77  fof(f70,plain,(
% 2.76/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f30])).
% 2.76/0.77  fof(f30,plain,(
% 2.76/0.77    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.77    inference(ennf_transformation,[],[f9])).
% 2.76/0.77  fof(f9,axiom,(
% 2.76/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.76/0.77  fof(f5401,plain,(
% 2.76/0.77    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_4),
% 2.76/0.77    inference(resolution,[],[f5344,f78])).
% 2.76/0.77  fof(f78,plain,(
% 2.76/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f33])).
% 2.76/0.77  fof(f33,plain,(
% 2.76/0.77    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.77    inference(flattening,[],[f32])).
% 2.76/0.77  fof(f32,plain,(
% 2.76/0.77    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.77    inference(ennf_transformation,[],[f10])).
% 2.76/0.77  fof(f10,axiom,(
% 2.76/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.76/0.77  fof(f6827,plain,(
% 2.76/0.77    ~spl4_72 | ~spl4_73 | ~spl4_4),
% 2.76/0.77    inference(avatar_split_clause,[],[f6229,f416,f6824,f6820])).
% 2.76/0.77  fof(f6229,plain,(
% 2.76/0.77    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl4_4),
% 2.76/0.77    inference(forward_demodulation,[],[f6228,f418])).
% 2.76/0.77  fof(f6228,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl4_4),
% 2.76/0.77    inference(forward_demodulation,[],[f568,f418])).
% 2.76/0.77  fof(f568,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 2.76/0.77    inference(global_subsumption,[],[f220,f221,f293,f294,f335,f374,f410])).
% 2.76/0.77  fof(f374,plain,(
% 2.76/0.77    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(forward_demodulation,[],[f37,f41])).
% 2.76/0.77  fof(f37,plain,(
% 2.76/0.77    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f335,plain,(
% 2.76/0.77    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(forward_demodulation,[],[f36,f41])).
% 2.76/0.77  fof(f36,plain,(
% 2.76/0.77    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f294,plain,(
% 2.76/0.77    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 2.76/0.77    inference(global_subsumption,[],[f42,f45,f46,f151,f255,f285])).
% 2.76/0.77  fof(f285,plain,(
% 2.76/0.77    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.76/0.77    inference(resolution,[],[f253,f93])).
% 2.76/0.77  fof(f93,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(duplicate_literal_removal,[],[f80])).
% 2.76/0.77  fof(f80,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(equality_resolution,[],[f54])).
% 2.76/0.77  fof(f54,plain,(
% 2.76/0.77    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f24])).
% 2.76/0.77  fof(f24,plain,(
% 2.76/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.76/0.77    inference(flattening,[],[f23])).
% 2.76/0.77  fof(f23,plain,(
% 2.76/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.76/0.77    inference(ennf_transformation,[],[f15])).
% 2.76/0.77  fof(f15,axiom,(
% 2.76/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 2.76/0.77  fof(f255,plain,(
% 2.76/0.77    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.76/0.77    inference(resolution,[],[f160,f60])).
% 2.76/0.77  fof(f60,plain,(
% 2.76/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 2.76/0.77    inference(cnf_transformation,[],[f28])).
% 2.76/0.77  fof(f28,plain,(
% 2.76/0.77    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.76/0.77    inference(ennf_transformation,[],[f11])).
% 2.76/0.77  fof(f11,axiom,(
% 2.76/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 2.76/0.77  fof(f160,plain,(
% 2.76/0.77    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.76/0.77    inference(resolution,[],[f48,f50])).
% 2.76/0.77  fof(f50,plain,(
% 2.76/0.77    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.76/0.77    inference(cnf_transformation,[],[f20])).
% 2.76/0.77  fof(f20,plain,(
% 2.76/0.77    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.76/0.77    inference(ennf_transformation,[],[f12])).
% 2.76/0.77  fof(f12,axiom,(
% 2.76/0.77    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.76/0.77  fof(f48,plain,(
% 2.76/0.77    l1_pre_topc(sK0)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f151,plain,(
% 2.76/0.77    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.76/0.77    inference(global_subsumption,[],[f48,f142])).
% 2.76/0.77  fof(f142,plain,(
% 2.76/0.77    ~l1_pre_topc(sK0) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.76/0.77    inference(resolution,[],[f47,f52])).
% 2.76/0.77  fof(f52,plain,(
% 2.76/0.77    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 2.76/0.77    inference(cnf_transformation,[],[f22])).
% 2.76/0.77  fof(f22,plain,(
% 2.76/0.77    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.76/0.77    inference(flattening,[],[f21])).
% 2.76/0.77  fof(f21,plain,(
% 2.76/0.77    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.76/0.77    inference(ennf_transformation,[],[f13])).
% 2.76/0.77  fof(f13,axiom,(
% 2.76/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 2.76/0.77  fof(f47,plain,(
% 2.76/0.77    v2_pre_topc(sK0)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f46,plain,(
% 2.76/0.77    l1_pre_topc(sK1)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f45,plain,(
% 2.76/0.77    v2_pre_topc(sK1)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f42,plain,(
% 2.76/0.77    v1_funct_1(sK2)),
% 2.76/0.77    inference(cnf_transformation,[],[f19])).
% 2.76/0.77  fof(f293,plain,(
% 2.76/0.77    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.76/0.77    inference(global_subsumption,[],[f42,f45,f46,f151,f255,f284])).
% 2.76/0.77  fof(f284,plain,(
% 2.76/0.77    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.76/0.77    inference(resolution,[],[f253,f94])).
% 2.76/0.77  fof(f94,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(duplicate_literal_removal,[],[f81])).
% 2.76/0.77  fof(f81,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(equality_resolution,[],[f53])).
% 2.76/0.77  fof(f53,plain,(
% 2.76/0.77    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f24])).
% 2.76/0.77  fof(f221,plain,(
% 2.76/0.77    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 2.76/0.77    inference(global_subsumption,[],[f186])).
% 2.76/0.77  fof(f186,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f181])).
% 2.76/0.77  fof(f181,plain,(
% 2.76/0.77    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(resolution,[],[f43,f95])).
% 2.76/0.77  fof(f95,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(duplicate_literal_removal,[],[f82])).
% 2.76/0.77  fof(f82,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(equality_resolution,[],[f56])).
% 2.76/0.77  fof(f56,plain,(
% 2.76/0.77    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f26])).
% 2.76/0.77  fof(f26,plain,(
% 2.76/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.76/0.77    inference(flattening,[],[f25])).
% 2.76/0.77  fof(f25,plain,(
% 2.76/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.76/0.77    inference(ennf_transformation,[],[f14])).
% 2.76/0.77  fof(f14,axiom,(
% 2.76/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.76/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.76/0.77  fof(f220,plain,(
% 2.76/0.77    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(global_subsumption,[],[f185])).
% 2.76/0.77  fof(f185,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.76/0.77    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f180])).
% 2.76/0.77  fof(f180,plain,(
% 2.76/0.77    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 2.76/0.77    inference(resolution,[],[f43,f96])).
% 2.76/0.77  fof(f96,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(duplicate_literal_removal,[],[f83])).
% 2.76/0.77  fof(f83,plain,(
% 2.76/0.77    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.76/0.77    inference(equality_resolution,[],[f55])).
% 2.76/0.77  fof(f55,plain,(
% 2.76/0.77    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f26])).
% 2.76/0.77  fof(f5062,plain,(
% 2.76/0.77    ~spl4_32 | ~spl4_46 | spl4_57),
% 2.76/0.77    inference(avatar_contradiction_clause,[],[f5042])).
% 2.76/0.77  fof(f5042,plain,(
% 2.76/0.77    $false | (~spl4_32 | ~spl4_46 | spl4_57)),
% 2.76/0.77    inference(resolution,[],[f4915,f2979])).
% 2.76/0.77  fof(f2979,plain,(
% 2.76/0.77    ( ! [X6] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X6)) ) | ~spl4_32),
% 2.76/0.77    inference(avatar_component_clause,[],[f2978])).
% 2.76/0.77  fof(f2978,plain,(
% 2.76/0.77    spl4_32 <=> ! [X6] : v1_funct_2(k1_xboole_0,k1_xboole_0,X6)),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.76/0.77  fof(f4915,plain,(
% 2.76/0.77    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_46 | spl4_57)),
% 2.76/0.77    inference(backward_demodulation,[],[f4584,f4718])).
% 2.76/0.77  fof(f4718,plain,(
% 2.76/0.77    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_46 | spl4_57)),
% 2.76/0.77    inference(resolution,[],[f3622,f4584])).
% 2.76/0.77  fof(f3622,plain,(
% 2.76/0.77    ( ! [X19] : (v1_funct_2(k1_xboole_0,X19,k1_xboole_0) | k1_xboole_0 = X19) ) | ~spl4_46),
% 2.76/0.77    inference(avatar_component_clause,[],[f3621])).
% 2.76/0.77  fof(f3621,plain,(
% 2.76/0.77    spl4_46 <=> ! [X19] : (k1_xboole_0 = X19 | v1_funct_2(k1_xboole_0,X19,k1_xboole_0))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.76/0.77  fof(f4584,plain,(
% 2.76/0.77    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | spl4_57),
% 2.76/0.77    inference(avatar_component_clause,[],[f4582])).
% 2.76/0.77  fof(f4582,plain,(
% 2.76/0.77    spl4_57 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 2.76/0.77  fof(f4656,plain,(
% 2.76/0.77    spl4_46 | ~spl4_8),
% 2.76/0.77    inference(avatar_split_clause,[],[f4597,f771,f3621])).
% 2.76/0.77  fof(f771,plain,(
% 2.76/0.77    spl4_8 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.76/0.77  fof(f4597,plain,(
% 2.76/0.77    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 2.76/0.77    inference(forward_demodulation,[],[f92,f86])).
% 2.76/0.77  fof(f92,plain,(
% 2.76/0.77    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 2.76/0.77    inference(equality_resolution,[],[f91])).
% 2.76/0.77  fof(f91,plain,(
% 2.76/0.77    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 2.76/0.77    inference(equality_resolution,[],[f73])).
% 2.76/0.77  fof(f73,plain,(
% 2.76/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 2.76/0.77    inference(cnf_transformation,[],[f33])).
% 2.76/0.77  fof(f4585,plain,(
% 2.76/0.77    ~spl4_57 | ~spl4_8 | ~spl4_3 | ~spl4_11),
% 2.76/0.77    inference(avatar_split_clause,[],[f4580,f1091,f412,f771,f4582])).
% 2.76/0.77  fof(f412,plain,(
% 2.76/0.77    spl4_3 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.76/0.77  fof(f1091,plain,(
% 2.76/0.77    spl4_11 <=> k1_xboole_0 = sK2),
% 2.76/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.76/0.77  fof(f4580,plain,(
% 2.76/0.77    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_3 | ~spl4_11)),
% 2.76/0.77    inference(forward_demodulation,[],[f4579,f1093])).
% 2.76/0.77  fof(f1093,plain,(
% 2.76/0.77    k1_xboole_0 = sK2 | ~spl4_11),
% 2.76/0.77    inference(avatar_component_clause,[],[f1091])).
% 2.76/0.77  fof(f4579,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_3 | ~spl4_11)),
% 2.76/0.77    inference(forward_demodulation,[],[f4578,f86])).
% 2.76/0.77  fof(f4578,plain,(
% 2.76/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_3 | ~spl4_11)),
% 2.76/0.77    inference(forward_demodulation,[],[f4577,f414])).
% 2.76/0.77  fof(f414,plain,(
% 2.76/0.77    k1_xboole_0 = u1_struct_0(sK1) | ~spl4_3),
% 2.76/0.77    inference(avatar_component_clause,[],[f412])).
% 2.76/0.77  fof(f4577,plain,(
% 2.76/0.77    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl4_3 | ~spl4_11)),
% 2.76/0.77    inference(forward_demodulation,[],[f4576,f1093])).
% 2.76/0.77  fof(f4576,plain,(
% 2.76/0.77    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl4_3),
% 2.76/0.77    inference(forward_demodulation,[],[f845,f414])).
% 3.31/0.77  fof(f845,plain,(
% 3.31/0.77    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 3.31/0.77    inference(global_subsumption,[],[f569])).
% 3.31/0.77  fof(f569,plain,(
% 3.31/0.77    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 3.31/0.77    inference(global_subsumption,[],[f568])).
% 3.31/0.77  fof(f3933,plain,(
% 3.31/0.77    ~spl4_32 | spl4_52),
% 3.31/0.77    inference(avatar_contradiction_clause,[],[f3923])).
% 3.31/0.77  fof(f3923,plain,(
% 3.31/0.77    $false | (~spl4_32 | spl4_52)),
% 3.31/0.77    inference(resolution,[],[f3921,f2979])).
% 3.31/0.77  fof(f3921,plain,(
% 3.31/0.77    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl4_52),
% 3.31/0.77    inference(avatar_component_clause,[],[f3919])).
% 3.31/0.77  fof(f3919,plain,(
% 3.31/0.77    spl4_52 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.31/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 3.31/0.77  fof(f3922,plain,(
% 3.31/0.77    ~spl4_8 | ~spl4_52 | ~spl4_4 | ~spl4_11 | ~spl4_15),
% 3.31/0.77    inference(avatar_split_clause,[],[f3917,f1319,f1091,f416,f3919,f771])).
% 3.31/0.77  fof(f1319,plain,(
% 3.31/0.77    spl4_15 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 3.31/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.31/0.77  fof(f3917,plain,(
% 3.31/0.77    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_11 | ~spl4_15)),
% 3.31/0.77    inference(forward_demodulation,[],[f3916,f1093])).
% 3.31/0.77  fof(f3916,plain,(
% 3.31/0.77    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_11 | ~spl4_15)),
% 3.31/0.77    inference(forward_demodulation,[],[f3915,f2150])).
% 3.31/0.77  fof(f2150,plain,(
% 3.31/0.77    k1_xboole_0 = u1_struct_0(sK0) | (~spl4_4 | ~spl4_15)),
% 3.31/0.77    inference(forward_demodulation,[],[f418,f1321])).
% 3.31/0.77  fof(f1321,plain,(
% 3.31/0.77    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_15),
% 3.31/0.77    inference(avatar_component_clause,[],[f1319])).
% 3.31/0.77  fof(f3915,plain,(
% 3.31/0.77    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_4 | ~spl4_11 | ~spl4_15)),
% 3.31/0.77    inference(forward_demodulation,[],[f3914,f1093])).
% 3.31/0.77  fof(f3914,plain,(
% 3.31/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_4 | ~spl4_15)),
% 3.31/0.77    inference(forward_demodulation,[],[f3913,f87])).
% 3.31/0.77  fof(f87,plain,(
% 3.31/0.77    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.31/0.77    inference(equality_resolution,[],[f67])).
% 3.31/0.77  fof(f67,plain,(
% 3.31/0.77    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 3.31/0.77    inference(cnf_transformation,[],[f2])).
% 3.31/0.77  fof(f3913,plain,(
% 3.31/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_4 | ~spl4_15)),
% 3.31/0.77    inference(forward_demodulation,[],[f570,f2150])).
% 3.31/0.77  fof(f570,plain,(
% 3.31/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.31/0.77    inference(global_subsumption,[],[f222,f223,f291,f292,f335,f374,f410])).
% 3.31/0.77  fof(f292,plain,(
% 3.31/0.77    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.31/0.77    inference(global_subsumption,[],[f42,f47,f48,f114,f208,f283])).
% 3.31/0.77  fof(f283,plain,(
% 3.31/0.77    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.31/0.77    inference(resolution,[],[f253,f95])).
% 3.31/0.77  fof(f208,plain,(
% 3.31/0.77    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.31/0.77    inference(resolution,[],[f123,f60])).
% 3.31/0.77  fof(f123,plain,(
% 3.31/0.77    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.31/0.77    inference(resolution,[],[f46,f50])).
% 3.31/0.77  fof(f114,plain,(
% 3.31/0.77    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.31/0.77    inference(global_subsumption,[],[f46,f105])).
% 3.31/0.77  fof(f105,plain,(
% 3.31/0.77    ~l1_pre_topc(sK1) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.31/0.77    inference(resolution,[],[f45,f52])).
% 3.31/0.77  fof(f291,plain,(
% 3.31/0.77    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.31/0.77    inference(global_subsumption,[],[f42,f47,f48,f114,f208,f282])).
% 3.31/0.77  fof(f282,plain,(
% 3.31/0.77    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.31/0.77    inference(resolution,[],[f253,f96])).
% 3.31/0.77  fof(f223,plain,(
% 3.31/0.77    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.31/0.77    inference(global_subsumption,[],[f188])).
% 3.31/0.77  fof(f188,plain,(
% 3.31/0.77    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.31/0.77    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f183])).
% 3.31/0.77  fof(f183,plain,(
% 3.31/0.77    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.31/0.77    inference(resolution,[],[f43,f93])).
% 3.31/0.78  fof(f222,plain,(
% 3.31/0.78    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.31/0.78    inference(global_subsumption,[],[f187])).
% 3.31/0.78  fof(f187,plain,(
% 3.31/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.31/0.78    inference(global_subsumption,[],[f44,f42,f45,f46,f47,f48,f182])).
% 3.31/0.78  fof(f182,plain,(
% 3.31/0.78    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.31/0.78    inference(resolution,[],[f43,f94])).
% 3.31/0.78  fof(f2980,plain,(
% 3.31/0.78    spl4_32 | ~spl4_8 | ~spl4_22 | ~spl4_11 | ~spl4_15),
% 3.31/0.78    inference(avatar_split_clause,[],[f2976,f1319,f1091,f2020,f771,f2978])).
% 3.31/0.78  fof(f2020,plain,(
% 3.31/0.78    spl4_22 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 3.31/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 3.31/0.78  fof(f2976,plain,(
% 3.31/0.78    ( ! [X6] : (~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X6)) ) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(forward_demodulation,[],[f2975,f87])).
% 3.31/0.78  fof(f2975,plain,(
% 3.31/0.78    ( ! [X6] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X6) | ~v4_relat_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X6))) ) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(forward_demodulation,[],[f2971,f87])).
% 3.31/0.78  fof(f2971,plain,(
% 3.31/0.78    ( ! [X6] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X6) | ~v4_relat_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X6))) ) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(trivial_inequality_removal,[],[f2970])).
% 3.31/0.78  fof(f2970,plain,(
% 3.31/0.78    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X6) | ~v4_relat_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X6))) ) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(superposition,[],[f89,f2956])).
% 3.31/0.78  fof(f2956,plain,(
% 3.31/0.78    ( ! [X23,X22] : (k1_xboole_0 = k1_relset_1(X22,X23,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23))) ) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(forward_demodulation,[],[f2955,f1766])).
% 3.31/0.78  fof(f1766,plain,(
% 3.31/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(forward_demodulation,[],[f1321,f1093])).
% 3.31/0.78  fof(f2955,plain,(
% 3.31/0.78    ( ! [X23,X22] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X22,X23,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23))) ) | (~spl4_11 | ~spl4_15)),
% 3.31/0.78    inference(forward_demodulation,[],[f2954,f1766])).
% 3.31/0.78  fof(f2954,plain,(
% 3.31/0.78    ( ! [X23,X22] : (k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relset_1(X22,X23,k1_relat_1(k1_xboole_0)) | ~v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23))) ) | ~spl4_11),
% 3.31/0.78    inference(forward_demodulation,[],[f2953,f1093])).
% 3.31/0.78  fof(f2953,plain,(
% 3.31/0.78    ( ! [X23,X22] : (~v4_relat_1(k1_xboole_0,k2_zfmisc_1(X22,X23)) | k1_relset_1(X22,X23,k1_relat_1(sK2)) = k1_relat_1(k1_relat_1(sK2))) ) | ~spl4_11),
% 3.31/0.78    inference(forward_demodulation,[],[f313,f1093])).
% 3.31/0.78  fof(f313,plain,(
% 3.31/0.78    ( ! [X23,X22] : (k1_relset_1(X22,X23,k1_relat_1(sK2)) = k1_relat_1(k1_relat_1(sK2)) | ~v4_relat_1(sK2,k2_zfmisc_1(X22,X23))) )),
% 3.31/0.78    inference(resolution,[],[f299,f70])).
% 3.31/0.78  fof(f299,plain,(
% 3.31/0.78    ( ! [X0] : (m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) | ~v4_relat_1(sK2,X0)) )),
% 3.31/0.78    inference(resolution,[],[f225,f64])).
% 3.31/0.78  fof(f225,plain,(
% 3.31/0.78    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v4_relat_1(sK2,X0)) )),
% 3.31/0.78    inference(resolution,[],[f218,f58])).
% 3.31/0.78  fof(f58,plain,(
% 3.31/0.78    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 3.31/0.78    inference(cnf_transformation,[],[f27])).
% 3.31/0.78  fof(f27,plain,(
% 3.31/0.78    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/0.78    inference(ennf_transformation,[],[f6])).
% 3.31/0.78  fof(f6,axiom,(
% 3.31/0.78    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.31/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 3.31/0.78  fof(f218,plain,(
% 3.31/0.78    v1_relat_1(sK2)),
% 3.31/0.78    inference(resolution,[],[f44,f69])).
% 3.31/0.78  fof(f69,plain,(
% 3.31/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.31/0.78    inference(cnf_transformation,[],[f29])).
% 3.31/0.78  fof(f29,plain,(
% 3.31/0.78    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.78    inference(ennf_transformation,[],[f7])).
% 3.31/0.78  fof(f7,axiom,(
% 3.31/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.31/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.31/0.78  fof(f89,plain,(
% 3.31/0.78    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 3.31/0.78    inference(equality_resolution,[],[f75])).
% 3.31/0.78  fof(f75,plain,(
% 3.31/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 3.31/0.78    inference(cnf_transformation,[],[f33])).
% 3.31/0.78  fof(f2112,plain,(
% 3.31/0.78    ~spl4_8 | spl4_22),
% 3.31/0.78    inference(avatar_split_clause,[],[f2038,f2020,f771])).
% 3.31/0.78  fof(f2038,plain,(
% 3.31/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_22),
% 3.31/0.78    inference(forward_demodulation,[],[f2029,f87])).
% 3.31/0.78  fof(f2029,plain,(
% 3.31/0.78    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl4_22),
% 3.31/0.78    inference(resolution,[],[f2022,f71])).
% 3.31/0.78  fof(f71,plain,(
% 3.31/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.31/0.78    inference(cnf_transformation,[],[f31])).
% 3.31/0.78  fof(f31,plain,(
% 3.31/0.78    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.78    inference(ennf_transformation,[],[f8])).
% 3.31/0.78  fof(f8,axiom,(
% 3.31/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.31/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.31/0.78  fof(f2022,plain,(
% 3.31/0.78    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | spl4_22),
% 3.31/0.78    inference(avatar_component_clause,[],[f2020])).
% 3.31/0.78  fof(f1761,plain,(
% 3.31/0.78    ~spl4_8 | ~spl4_11 | spl4_14),
% 3.31/0.78    inference(avatar_split_clause,[],[f1671,f1315,f1091,f771])).
% 3.31/0.78  fof(f1315,plain,(
% 3.31/0.78    spl4_14 <=> v4_relat_1(sK2,k1_xboole_0)),
% 3.31/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.31/0.78  fof(f1671,plain,(
% 3.31/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_11 | spl4_14)),
% 3.31/0.78    inference(forward_demodulation,[],[f1663,f87])).
% 3.31/0.78  fof(f1663,plain,(
% 3.31/0.78    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl4_11 | spl4_14)),
% 3.31/0.78    inference(resolution,[],[f1573,f71])).
% 3.31/0.78  fof(f1573,plain,(
% 3.31/0.78    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_11 | spl4_14)),
% 3.31/0.78    inference(backward_demodulation,[],[f1317,f1093])).
% 3.31/0.78  fof(f1317,plain,(
% 3.31/0.78    ~v4_relat_1(sK2,k1_xboole_0) | spl4_14),
% 3.31/0.78    inference(avatar_component_clause,[],[f1315])).
% 3.31/0.78  fof(f1322,plain,(
% 3.31/0.78    ~spl4_14 | spl4_15),
% 3.31/0.78    inference(avatar_split_clause,[],[f756,f1319,f1315])).
% 3.31/0.78  fof(f756,plain,(
% 3.31/0.78    k1_xboole_0 = k1_relat_1(sK2) | ~v4_relat_1(sK2,k1_xboole_0)),
% 3.31/0.78    inference(resolution,[],[f734,f49])).
% 3.31/0.78  fof(f49,plain,(
% 3.31/0.78    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.31/0.78    inference(cnf_transformation,[],[f3])).
% 3.31/0.78  fof(f3,axiom,(
% 3.31/0.78    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.31/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.31/0.78  fof(f734,plain,(
% 3.31/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK2))) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0)) )),
% 3.31/0.78    inference(resolution,[],[f300,f65])).
% 3.31/0.78  fof(f300,plain,(
% 3.31/0.78    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK2)) | ~v4_relat_1(sK2,X1) | k1_relat_1(sK2) = X1) )),
% 3.31/0.78    inference(resolution,[],[f225,f63])).
% 3.31/0.78  fof(f63,plain,(
% 3.31/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.31/0.78    inference(cnf_transformation,[],[f1])).
% 3.31/0.78  fof(f1,axiom,(
% 3.31/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.31/0.78  fof(f1286,plain,(
% 3.31/0.78    spl4_11 | ~spl4_13 | ~spl4_12),
% 3.31/0.78    inference(avatar_split_clause,[],[f1138,f1095,f1283,f1091])).
% 3.31/0.78  fof(f1095,plain,(
% 3.31/0.78    spl4_12 <=> r1_tarski(k1_xboole_0,sK2)),
% 3.31/0.78    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.31/0.78  fof(f1138,plain,(
% 3.31/0.78    ~r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 | ~spl4_12),
% 3.31/0.78    inference(resolution,[],[f1096,f63])).
% 3.31/0.78  fof(f1096,plain,(
% 3.31/0.78    r1_tarski(k1_xboole_0,sK2) | ~spl4_12),
% 3.31/0.78    inference(avatar_component_clause,[],[f1095])).
% 3.31/0.78  fof(f1131,plain,(
% 3.31/0.78    spl4_12),
% 3.31/0.78    inference(avatar_contradiction_clause,[],[f1122])).
% 3.31/0.78  fof(f1122,plain,(
% 3.31/0.78    $false | spl4_12),
% 3.31/0.78    inference(resolution,[],[f1099,f49])).
% 3.31/0.78  fof(f1099,plain,(
% 3.31/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | spl4_12),
% 3.31/0.78    inference(resolution,[],[f1097,f65])).
% 3.31/0.78  fof(f1097,plain,(
% 3.31/0.78    ~r1_tarski(k1_xboole_0,sK2) | spl4_12),
% 3.31/0.78    inference(avatar_component_clause,[],[f1095])).
% 3.31/0.78  fof(f1098,plain,(
% 3.31/0.78    spl4_11 | ~spl4_12 | ~spl4_3),
% 3.31/0.78    inference(avatar_split_clause,[],[f814,f412,f1095,f1091])).
% 3.31/0.78  fof(f814,plain,(
% 3.31/0.78    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl4_3),
% 3.31/0.78    inference(resolution,[],[f468,f63])).
% 3.31/0.78  fof(f468,plain,(
% 3.31/0.78    r1_tarski(sK2,k1_xboole_0) | ~spl4_3),
% 3.31/0.78    inference(forward_demodulation,[],[f427,f86])).
% 3.31/0.78  fof(f427,plain,(
% 3.31/0.78    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | ~spl4_3),
% 3.31/0.78    inference(backward_demodulation,[],[f219,f414])).
% 3.31/0.78  fof(f219,plain,(
% 3.31/0.78    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 3.31/0.78    inference(resolution,[],[f44,f65])).
% 3.31/0.78  fof(f784,plain,(
% 3.31/0.78    spl4_8),
% 3.31/0.78    inference(avatar_contradiction_clause,[],[f775])).
% 3.31/0.78  fof(f775,plain,(
% 3.31/0.78    $false | spl4_8),
% 3.31/0.78    inference(resolution,[],[f773,f49])).
% 3.31/0.78  fof(f773,plain,(
% 3.31/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_8),
% 3.31/0.78    inference(avatar_component_clause,[],[f771])).
% 3.31/0.78  fof(f419,plain,(
% 3.31/0.78    spl4_3 | spl4_4),
% 3.31/0.78    inference(avatar_split_clause,[],[f408,f416,f412])).
% 3.31/0.78  fof(f408,plain,(
% 3.31/0.78    u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1)),
% 3.31/0.78    inference(global_subsumption,[],[f43,f44,f405])).
% 3.31/0.78  fof(f405,plain,(
% 3.31/0.78    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.31/0.78    inference(superposition,[],[f217,f78])).
% 3.31/0.78  fof(f217,plain,(
% 3.31/0.78    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 3.31/0.78    inference(resolution,[],[f44,f70])).
% 3.31/0.78  % SZS output end Proof for theBenchmark
% 3.31/0.78  % (14972)------------------------------
% 3.31/0.78  % (14972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.78  % (14972)Termination reason: Refutation
% 3.31/0.78  
% 3.31/0.78  % (14972)Memory used [KB]: 16247
% 3.31/0.78  % (14972)Time elapsed: 0.367 s
% 3.31/0.78  % (14972)------------------------------
% 3.31/0.78  % (14972)------------------------------
% 3.31/0.78  % (14951)Success in time 0.425 s
%------------------------------------------------------------------------------
