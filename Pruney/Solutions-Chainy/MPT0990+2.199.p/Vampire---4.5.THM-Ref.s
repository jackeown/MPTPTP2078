%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:03 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 457 expanded)
%              Number of leaves         :   50 ( 172 expanded)
%              Depth                    :    8
%              Number of atoms          :  778 (2226 expanded)
%              Number of equality atoms :  163 ( 636 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5252)Termination reason: Refutation not found, incomplete strategy

% (5252)Memory used [KB]: 11001
% (5252)Time elapsed: 0.161 s
% (5252)------------------------------
% (5252)------------------------------
fof(f789,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f104,f108,f112,f127,f129,f147,f175,f177,f179,f225,f232,f258,f285,f287,f289,f300,f348,f478,f485,f497,f581,f620,f628,f651,f658,f666,f674,f704,f723,f729,f749,f753,f758,f784])).

fof(f784,plain,
    ( ~ spl4_20
    | ~ spl4_77 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_77 ),
    inference(subsumption_resolution,[],[f46,f760])).

fof(f760,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_20
    | ~ spl4_77 ),
    inference(forward_demodulation,[],[f687,f245])).

fof(f245,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl4_20
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f687,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f685])).

fof(f685,plain,
    ( spl4_77
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f758,plain,
    ( ~ spl4_20
    | ~ spl4_28
    | spl4_81 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_28
    | spl4_81 ),
    inference(subsumption_resolution,[],[f297,f755])).

fof(f755,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_20
    | spl4_81 ),
    inference(forward_demodulation,[],[f703,f245])).

fof(f703,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_81 ),
    inference(avatar_component_clause,[],[f701])).

fof(f701,plain,
    ( spl4_81
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f297,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl4_28
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f753,plain,
    ( ~ spl4_6
    | ~ spl4_20
    | spl4_80 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_20
    | spl4_80 ),
    inference(trivial_inequality_removal,[],[f751])).

fof(f751,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_6
    | ~ spl4_20
    | spl4_80 ),
    inference(forward_demodulation,[],[f750,f125])).

fof(f125,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f750,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_20
    | spl4_80 ),
    inference(forward_demodulation,[],[f699,f245])).

fof(f699,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_80 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl4_80
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f749,plain,
    ( ~ spl4_20
    | spl4_79 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl4_20
    | spl4_79 ),
    inference(subsumption_resolution,[],[f43,f731])).

fof(f731,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_20
    | spl4_79 ),
    inference(forward_demodulation,[],[f695,f245])).

fof(f695,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_79 ),
    inference(avatar_component_clause,[],[f693])).

fof(f693,plain,
    ( spl4_79
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f729,plain,
    ( ~ spl4_20
    | spl4_78 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | ~ spl4_20
    | spl4_78 ),
    inference(unit_resulting_resolution,[],[f60,f49,f724,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f724,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_20
    | spl4_78 ),
    inference(forward_demodulation,[],[f691,f245])).

fof(f691,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_78 ),
    inference(avatar_component_clause,[],[f689])).

fof(f689,plain,
    ( spl4_78
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f723,plain,
    ( ~ spl4_20
    | spl4_75 ),
    inference(avatar_contradiction_clause,[],[f722])).

fof(f722,plain,
    ( $false
    | ~ spl4_20
    | spl4_75 ),
    inference(subsumption_resolution,[],[f47,f708])).

fof(f708,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_20
    | spl4_75 ),
    inference(superposition,[],[f678,f245])).

fof(f678,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_75 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl4_75
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f704,plain,
    ( spl4_77
    | ~ spl4_78
    | ~ spl4_79
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_75
    | ~ spl4_80
    | ~ spl4_81
    | ~ spl4_57
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f683,f655,f493,f701,f697,f676,f88,f161,f693,f689,f685])).

fof(f161,plain,
    ( spl4_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f88,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f493,plain,
    ( spl4_57
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f655,plain,
    ( spl4_73
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f683,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_57
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f670,f495])).

fof(f495,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f493])).

fof(f670,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_73 ),
    inference(superposition,[],[f79,f657])).

fof(f657,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f655])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f674,plain,
    ( ~ spl4_1
    | ~ spl4_21
    | ~ spl4_11
    | spl4_23
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f673,f655,f255,f161,f247,f88])).

fof(f247,plain,
    ( spl4_21
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f255,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f673,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f668,f78])).

fof(f78,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f668,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_73 ),
    inference(superposition,[],[f57,f657])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f666,plain,
    ( spl4_22
    | ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | spl4_22
    | ~ spl4_57 ),
    inference(trivial_inequality_removal,[],[f664])).

fof(f664,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_22
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f253,f495])).

fof(f253,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_22
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f658,plain,
    ( spl4_73
    | spl4_70
    | ~ spl4_21
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_55
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f490,f471,f475,f157,f161,f247,f613,f655])).

fof(f613,plain,
    ( spl4_70
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f157,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f475,plain,
    ( spl4_55
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f471,plain,
    ( spl4_54
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f490,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f488])).

fof(f488,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_54 ),
    inference(superposition,[],[f62,f473])).

fof(f473,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f471])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

% (5269)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (5270)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f651,plain,(
    ~ spl4_70 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl4_70 ),
    inference(subsumption_resolution,[],[f44,f615])).

fof(f615,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f613])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f628,plain,(
    spl4_71 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | spl4_71 ),
    inference(unit_resulting_resolution,[],[f75,f619])).

fof(f619,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl4_71
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f53,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f620,plain,
    ( ~ spl4_55
    | ~ spl4_10
    | ~ spl4_11
    | spl4_70
    | spl4_21
    | ~ spl4_71
    | ~ spl4_8
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f609,f579,f144,f617,f247,f613,f161,f157,f475])).

fof(f144,plain,
    ( spl4_8
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f579,plain,
    ( spl4_65
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f609,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8
    | ~ spl4_65 ),
    inference(superposition,[],[f580,f146])).

fof(f146,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f580,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f579])).

fof(f581,plain,
    ( ~ spl4_9
    | spl4_65
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f577,f282,f119,f579,f153])).

fof(f153,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f119,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f282,plain,
    ( spl4_27
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f577,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f572])).

fof(f572,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f68,f41])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f497,plain,
    ( ~ spl4_10
    | spl4_57
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f489,f471,f493,f157])).

fof(f489,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_54 ),
    inference(superposition,[],[f61,f473])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f485,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl4_55 ),
    inference(subsumption_resolution,[],[f39,f477])).

fof(f477,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_55 ),
    inference(avatar_component_clause,[],[f475])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f478,plain,
    ( spl4_54
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f466,f475,f157,f153,f282,f119,f161,f471])).

fof(f466,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f348,plain,(
    ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f45,f276])).

fof(f276,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f300,plain,
    ( ~ spl4_3
    | ~ spl4_26
    | ~ spl4_9
    | spl4_28
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f299,f270,f295,f153,f278,f97])).

fof(f97,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f278,plain,
    ( spl4_26
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f270,plain,
    ( spl4_24
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f299,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f291,f78])).

fof(f291,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(superposition,[],[f57,f272])).

fof(f272,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f270])).

fof(f289,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f48,f284])).

fof(f284,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f282])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f287,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl4_26 ),
    inference(subsumption_resolution,[],[f43,f280])).

fof(f280,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f278])).

fof(f285,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_26
    | ~ spl4_9
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f268,f282,f119,f153,f278,f274,f270])).

fof(f268,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f62,f41])).

fof(f258,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_9
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f241,f186,f123,f255,f251,f161,f97,f153,f247,f88,f243])).

fof(f186,plain,
    ( spl4_14
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f241,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f240,f125])).

fof(f240,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_14 ),
    inference(superposition,[],[f79,f188])).

fof(f188,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f232,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_5
    | spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f229,f144,f186,f119,f161,f157,f153])).

fof(f229,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f71,f146])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f225,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f142,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f142,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f179,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f38,f163])).

fof(f163,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f177,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f40,f159])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f175,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f47,f155])).

fof(f155,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f147,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f137,f144,f140])).

fof(f137,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f133,f42])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f70,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f129,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f49,f121])).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f127,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f117,f123,f119])).

fof(f117,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f61])).

fof(f112,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f103])).

fof(f103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f108,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f60,f94])).

fof(f94,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f85,f101,f97])).

fof(f85,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f49])).

fof(f95,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f84,f92,f88])).

fof(f84,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:41:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.54  % (5247)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (5245)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (5253)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (5255)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (5242)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (5268)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (5246)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (5250)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (5249)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (5260)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (5259)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (5264)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (5267)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (5256)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.58  % (5258)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.58  % (5251)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.58  % (5244)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.58  % (5266)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.58  % (5271)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (5252)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.58  % (5248)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.72/0.58  % (5261)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.72/0.59  % (5263)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.72/0.59  % (5265)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.72/0.59  % (5243)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.72/0.59  % (5257)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.72/0.60  % (5252)Refutation not found, incomplete strategy% (5252)------------------------------
% 1.72/0.60  % (5252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (5258)Refutation not found, incomplete strategy% (5258)------------------------------
% 1.72/0.60  % (5258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (5258)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (5258)Memory used [KB]: 10746
% 1.72/0.60  % (5258)Time elapsed: 0.190 s
% 1.72/0.60  % (5258)------------------------------
% 1.72/0.60  % (5258)------------------------------
% 1.86/0.60  % (5254)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.86/0.61  % (5262)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.86/0.61  % (5255)Refutation found. Thanks to Tanya!
% 1.86/0.61  % SZS status Theorem for theBenchmark
% 1.86/0.61  % SZS output start Proof for theBenchmark
% 1.86/0.61  % (5252)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.61  
% 1.86/0.61  % (5252)Memory used [KB]: 11001
% 1.86/0.61  % (5252)Time elapsed: 0.161 s
% 1.86/0.61  % (5252)------------------------------
% 1.86/0.61  % (5252)------------------------------
% 1.86/0.61  fof(f789,plain,(
% 1.86/0.61    $false),
% 1.86/0.61    inference(avatar_sat_refutation,[],[f95,f104,f108,f112,f127,f129,f147,f175,f177,f179,f225,f232,f258,f285,f287,f289,f300,f348,f478,f485,f497,f581,f620,f628,f651,f658,f666,f674,f704,f723,f729,f749,f753,f758,f784])).
% 1.86/0.61  fof(f784,plain,(
% 1.86/0.61    ~spl4_20 | ~spl4_77),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f777])).
% 1.86/0.61  fof(f777,plain,(
% 1.86/0.61    $false | (~spl4_20 | ~spl4_77)),
% 1.86/0.61    inference(subsumption_resolution,[],[f46,f760])).
% 1.86/0.61  fof(f760,plain,(
% 1.86/0.61    sK3 = k2_funct_1(sK2) | (~spl4_20 | ~spl4_77)),
% 1.86/0.61    inference(forward_demodulation,[],[f687,f245])).
% 1.86/0.61  fof(f245,plain,(
% 1.86/0.61    sK2 = k2_funct_1(sK3) | ~spl4_20),
% 1.86/0.61    inference(avatar_component_clause,[],[f243])).
% 1.86/0.61  fof(f243,plain,(
% 1.86/0.61    spl4_20 <=> sK2 = k2_funct_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.86/0.61  fof(f687,plain,(
% 1.86/0.61    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_77),
% 1.86/0.61    inference(avatar_component_clause,[],[f685])).
% 1.86/0.61  fof(f685,plain,(
% 1.86/0.61    spl4_77 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 1.86/0.61  fof(f46,plain,(
% 1.86/0.61    sK3 != k2_funct_1(sK2)),
% 1.86/0.61    inference(cnf_transformation,[],[f19])).
% 1.86/0.61  fof(f19,plain,(
% 1.86/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.86/0.61    inference(flattening,[],[f18])).
% 1.86/0.61  fof(f18,plain,(
% 1.86/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.86/0.61    inference(ennf_transformation,[],[f17])).
% 1.86/0.61  fof(f17,negated_conjecture,(
% 1.86/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.86/0.61    inference(negated_conjecture,[],[f16])).
% 1.86/0.61  fof(f16,conjecture,(
% 1.86/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.86/0.61  fof(f758,plain,(
% 1.86/0.61    ~spl4_20 | ~spl4_28 | spl4_81),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f757])).
% 1.86/0.61  fof(f757,plain,(
% 1.86/0.61    $false | (~spl4_20 | ~spl4_28 | spl4_81)),
% 1.86/0.61    inference(subsumption_resolution,[],[f297,f755])).
% 1.86/0.61  fof(f755,plain,(
% 1.86/0.61    sK0 != k1_relat_1(sK2) | (~spl4_20 | spl4_81)),
% 1.86/0.61    inference(forward_demodulation,[],[f703,f245])).
% 1.86/0.61  fof(f703,plain,(
% 1.86/0.61    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_81),
% 1.86/0.61    inference(avatar_component_clause,[],[f701])).
% 1.86/0.61  fof(f701,plain,(
% 1.86/0.61    spl4_81 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 1.86/0.61  fof(f297,plain,(
% 1.86/0.61    sK0 = k1_relat_1(sK2) | ~spl4_28),
% 1.86/0.61    inference(avatar_component_clause,[],[f295])).
% 1.86/0.61  fof(f295,plain,(
% 1.86/0.61    spl4_28 <=> sK0 = k1_relat_1(sK2)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.86/0.61  fof(f753,plain,(
% 1.86/0.61    ~spl4_6 | ~spl4_20 | spl4_80),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f752])).
% 1.86/0.61  fof(f752,plain,(
% 1.86/0.61    $false | (~spl4_6 | ~spl4_20 | spl4_80)),
% 1.86/0.61    inference(trivial_inequality_removal,[],[f751])).
% 1.86/0.61  fof(f751,plain,(
% 1.86/0.61    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_6 | ~spl4_20 | spl4_80)),
% 1.86/0.61    inference(forward_demodulation,[],[f750,f125])).
% 1.86/0.61  fof(f125,plain,(
% 1.86/0.61    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.86/0.61    inference(avatar_component_clause,[],[f123])).
% 1.86/0.61  fof(f123,plain,(
% 1.86/0.61    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.86/0.61  fof(f750,plain,(
% 1.86/0.61    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_20 | spl4_80)),
% 1.86/0.61    inference(forward_demodulation,[],[f699,f245])).
% 1.86/0.61  fof(f699,plain,(
% 1.86/0.61    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_80),
% 1.86/0.61    inference(avatar_component_clause,[],[f697])).
% 1.86/0.61  fof(f697,plain,(
% 1.86/0.61    spl4_80 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 1.86/0.61  fof(f749,plain,(
% 1.86/0.61    ~spl4_20 | spl4_79),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f748])).
% 1.86/0.61  fof(f748,plain,(
% 1.86/0.61    $false | (~spl4_20 | spl4_79)),
% 1.86/0.61    inference(subsumption_resolution,[],[f43,f731])).
% 1.86/0.61  fof(f731,plain,(
% 1.86/0.61    ~v2_funct_1(sK2) | (~spl4_20 | spl4_79)),
% 1.86/0.61    inference(forward_demodulation,[],[f695,f245])).
% 1.86/0.61  fof(f695,plain,(
% 1.86/0.61    ~v2_funct_1(k2_funct_1(sK3)) | spl4_79),
% 1.86/0.61    inference(avatar_component_clause,[],[f693])).
% 1.86/0.61  fof(f693,plain,(
% 1.86/0.61    spl4_79 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 1.86/0.61  fof(f43,plain,(
% 1.86/0.61    v2_funct_1(sK2)),
% 1.86/0.61    inference(cnf_transformation,[],[f19])).
% 1.86/0.61  fof(f729,plain,(
% 1.86/0.61    ~spl4_20 | spl4_78),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f728])).
% 1.86/0.61  fof(f728,plain,(
% 1.86/0.61    $false | (~spl4_20 | spl4_78)),
% 1.86/0.61    inference(unit_resulting_resolution,[],[f60,f49,f724,f56])).
% 1.86/0.61  fof(f56,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f20])).
% 1.86/0.61  fof(f20,plain,(
% 1.86/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.86/0.61    inference(ennf_transformation,[],[f1])).
% 1.86/0.61  fof(f1,axiom,(
% 1.86/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.86/0.61  fof(f724,plain,(
% 1.86/0.61    ~v1_relat_1(sK2) | (~spl4_20 | spl4_78)),
% 1.86/0.61    inference(forward_demodulation,[],[f691,f245])).
% 1.86/0.61  fof(f691,plain,(
% 1.86/0.61    ~v1_relat_1(k2_funct_1(sK3)) | spl4_78),
% 1.86/0.61    inference(avatar_component_clause,[],[f689])).
% 1.86/0.61  fof(f689,plain,(
% 1.86/0.61    spl4_78 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 1.86/0.61  fof(f49,plain,(
% 1.86/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.86/0.61    inference(cnf_transformation,[],[f19])).
% 1.86/0.61  fof(f60,plain,(
% 1.86/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f2])).
% 1.86/0.61  fof(f2,axiom,(
% 1.86/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.86/0.61  fof(f723,plain,(
% 1.86/0.61    ~spl4_20 | spl4_75),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f722])).
% 1.86/0.61  fof(f722,plain,(
% 1.86/0.61    $false | (~spl4_20 | spl4_75)),
% 1.86/0.61    inference(subsumption_resolution,[],[f47,f708])).
% 1.86/0.61  fof(f708,plain,(
% 1.86/0.61    ~v1_funct_1(sK2) | (~spl4_20 | spl4_75)),
% 1.86/0.61    inference(superposition,[],[f678,f245])).
% 1.86/0.61  fof(f678,plain,(
% 1.86/0.61    ~v1_funct_1(k2_funct_1(sK3)) | spl4_75),
% 1.86/0.61    inference(avatar_component_clause,[],[f676])).
% 1.86/0.61  fof(f676,plain,(
% 1.86/0.61    spl4_75 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.86/0.61  fof(f47,plain,(
% 1.86/0.61    v1_funct_1(sK2)),
% 1.86/0.61    inference(cnf_transformation,[],[f19])).
% 1.86/0.61  fof(f704,plain,(
% 1.86/0.61    spl4_77 | ~spl4_78 | ~spl4_79 | ~spl4_11 | ~spl4_1 | ~spl4_75 | ~spl4_80 | ~spl4_81 | ~spl4_57 | ~spl4_73),
% 1.86/0.61    inference(avatar_split_clause,[],[f683,f655,f493,f701,f697,f676,f88,f161,f693,f689,f685])).
% 1.86/0.61  fof(f161,plain,(
% 1.86/0.61    spl4_11 <=> v1_funct_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.86/0.61  fof(f88,plain,(
% 1.86/0.61    spl4_1 <=> v1_relat_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.86/0.61  fof(f493,plain,(
% 1.86/0.61    spl4_57 <=> sK0 = k2_relat_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.86/0.61  fof(f655,plain,(
% 1.86/0.61    spl4_73 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.86/0.61  fof(f683,plain,(
% 1.86/0.61    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_57 | ~spl4_73)),
% 1.86/0.61    inference(forward_demodulation,[],[f670,f495])).
% 1.86/0.61  fof(f495,plain,(
% 1.86/0.61    sK0 = k2_relat_1(sK3) | ~spl4_57),
% 1.86/0.61    inference(avatar_component_clause,[],[f493])).
% 1.86/0.61  fof(f670,plain,(
% 1.86/0.61    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_73),
% 1.86/0.61    inference(superposition,[],[f79,f657])).
% 1.86/0.61  fof(f657,plain,(
% 1.86/0.61    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_73),
% 1.86/0.61    inference(avatar_component_clause,[],[f655])).
% 1.86/0.61  fof(f79,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.86/0.61    inference(definition_unfolding,[],[f59,f50])).
% 1.86/0.61  fof(f50,plain,(
% 1.86/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f12])).
% 1.86/0.61  fof(f12,axiom,(
% 1.86/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.86/0.61  fof(f59,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.86/0.61    inference(cnf_transformation,[],[f24])).
% 1.86/0.61  fof(f24,plain,(
% 1.86/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.86/0.61    inference(flattening,[],[f23])).
% 1.86/0.61  fof(f23,plain,(
% 1.86/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.86/0.61    inference(ennf_transformation,[],[f6])).
% 1.86/0.61  fof(f6,axiom,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.86/0.61  fof(f674,plain,(
% 1.86/0.61    ~spl4_1 | ~spl4_21 | ~spl4_11 | spl4_23 | ~spl4_73),
% 1.86/0.61    inference(avatar_split_clause,[],[f673,f655,f255,f161,f247,f88])).
% 1.86/0.61  fof(f247,plain,(
% 1.86/0.61    spl4_21 <=> v2_funct_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.86/0.61  fof(f255,plain,(
% 1.86/0.61    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.86/0.61  fof(f673,plain,(
% 1.86/0.61    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_73),
% 1.86/0.61    inference(forward_demodulation,[],[f668,f78])).
% 1.86/0.61  fof(f78,plain,(
% 1.86/0.61    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.86/0.61    inference(definition_unfolding,[],[f54,f50])).
% 1.86/0.61  fof(f54,plain,(
% 1.86/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.86/0.61    inference(cnf_transformation,[],[f3])).
% 1.86/0.61  fof(f3,axiom,(
% 1.86/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.86/0.61  fof(f668,plain,(
% 1.86/0.61    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_73),
% 1.86/0.61    inference(superposition,[],[f57,f657])).
% 1.86/0.61  fof(f57,plain,(
% 1.86/0.61    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f22])).
% 1.86/0.61  fof(f22,plain,(
% 1.86/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.86/0.61    inference(flattening,[],[f21])).
% 1.86/0.61  fof(f21,plain,(
% 1.86/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.86/0.61    inference(ennf_transformation,[],[f5])).
% 1.86/0.61  fof(f5,axiom,(
% 1.86/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.86/0.61  fof(f666,plain,(
% 1.86/0.61    spl4_22 | ~spl4_57),
% 1.86/0.61    inference(avatar_contradiction_clause,[],[f665])).
% 1.86/0.61  fof(f665,plain,(
% 1.86/0.61    $false | (spl4_22 | ~spl4_57)),
% 1.86/0.61    inference(trivial_inequality_removal,[],[f664])).
% 1.86/0.61  fof(f664,plain,(
% 1.86/0.61    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_22 | ~spl4_57)),
% 1.86/0.61    inference(forward_demodulation,[],[f253,f495])).
% 1.86/0.61  fof(f253,plain,(
% 1.86/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_22),
% 1.86/0.61    inference(avatar_component_clause,[],[f251])).
% 1.86/0.61  fof(f251,plain,(
% 1.86/0.61    spl4_22 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.86/0.61  fof(f658,plain,(
% 1.86/0.61    spl4_73 | spl4_70 | ~spl4_21 | ~spl4_11 | ~spl4_10 | ~spl4_55 | ~spl4_54),
% 1.86/0.61    inference(avatar_split_clause,[],[f490,f471,f475,f157,f161,f247,f613,f655])).
% 1.86/0.61  fof(f613,plain,(
% 1.86/0.61    spl4_70 <=> k1_xboole_0 = sK0),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 1.86/0.61  fof(f157,plain,(
% 1.86/0.61    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.86/0.61  fof(f475,plain,(
% 1.86/0.61    spl4_55 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.86/0.61  fof(f471,plain,(
% 1.86/0.61    spl4_54 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.86/0.61  fof(f490,plain,(
% 1.86/0.61    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_54),
% 1.86/0.61    inference(trivial_inequality_removal,[],[f488])).
% 1.86/0.61  fof(f488,plain,(
% 1.86/0.61    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_54),
% 1.86/0.61    inference(superposition,[],[f62,f473])).
% 1.86/0.61  fof(f473,plain,(
% 1.86/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_54),
% 1.86/0.61    inference(avatar_component_clause,[],[f471])).
% 1.86/0.61  fof(f62,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f27])).
% 1.86/0.61  fof(f27,plain,(
% 1.86/0.61    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.86/0.61    inference(flattening,[],[f26])).
% 1.86/0.61  fof(f26,plain,(
% 1.86/0.61    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.86/0.61    inference(ennf_transformation,[],[f15])).
% 1.86/0.61  % (5269)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.03/0.63  % (5270)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.03/0.63  fof(f15,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.03/0.63  fof(f651,plain,(
% 2.03/0.63    ~spl4_70),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f629])).
% 2.03/0.63  fof(f629,plain,(
% 2.03/0.63    $false | ~spl4_70),
% 2.03/0.63    inference(subsumption_resolution,[],[f44,f615])).
% 2.03/0.63  fof(f615,plain,(
% 2.03/0.63    k1_xboole_0 = sK0 | ~spl4_70),
% 2.03/0.63    inference(avatar_component_clause,[],[f613])).
% 2.03/0.63  fof(f44,plain,(
% 2.03/0.63    k1_xboole_0 != sK0),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f628,plain,(
% 2.03/0.63    spl4_71),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f625])).
% 2.03/0.63  fof(f625,plain,(
% 2.03/0.63    $false | spl4_71),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f75,f619])).
% 2.03/0.63  fof(f619,plain,(
% 2.03/0.63    ~v2_funct_1(k6_partfun1(sK0)) | spl4_71),
% 2.03/0.63    inference(avatar_component_clause,[],[f617])).
% 2.03/0.63  fof(f617,plain,(
% 2.03/0.63    spl4_71 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 2.03/0.63  fof(f75,plain,(
% 2.03/0.63    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.03/0.63    inference(definition_unfolding,[],[f53,f50])).
% 2.03/0.63  fof(f53,plain,(
% 2.03/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f4])).
% 2.03/0.63  fof(f4,axiom,(
% 2.03/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.03/0.63  fof(f620,plain,(
% 2.03/0.63    ~spl4_55 | ~spl4_10 | ~spl4_11 | spl4_70 | spl4_21 | ~spl4_71 | ~spl4_8 | ~spl4_65),
% 2.03/0.63    inference(avatar_split_clause,[],[f609,f579,f144,f617,f247,f613,f161,f157,f475])).
% 2.03/0.63  fof(f144,plain,(
% 2.03/0.63    spl4_8 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.03/0.63  fof(f579,plain,(
% 2.03/0.63    spl4_65 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 2.03/0.63  fof(f609,plain,(
% 2.03/0.63    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_8 | ~spl4_65)),
% 2.03/0.63    inference(superposition,[],[f580,f146])).
% 2.03/0.63  fof(f146,plain,(
% 2.03/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_8),
% 2.03/0.63    inference(avatar_component_clause,[],[f144])).
% 2.03/0.63  fof(f580,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_65),
% 2.03/0.63    inference(avatar_component_clause,[],[f579])).
% 2.03/0.63  fof(f581,plain,(
% 2.03/0.63    ~spl4_9 | spl4_65 | ~spl4_5 | ~spl4_27),
% 2.03/0.63    inference(avatar_split_clause,[],[f577,f282,f119,f579,f153])).
% 2.03/0.63  fof(f153,plain,(
% 2.03/0.63    spl4_9 <=> v1_funct_1(sK2)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.03/0.63  fof(f119,plain,(
% 2.03/0.63    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.03/0.63  fof(f282,plain,(
% 2.03/0.63    spl4_27 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.03/0.63  fof(f577,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.03/0.63    inference(trivial_inequality_removal,[],[f572])).
% 2.03/0.63  fof(f572,plain,(
% 2.03/0.63    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.03/0.63    inference(superposition,[],[f68,f41])).
% 2.03/0.63  fof(f41,plain,(
% 2.03/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f68,plain,(
% 2.03/0.63    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f31])).
% 2.03/0.63  fof(f31,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.03/0.63    inference(flattening,[],[f30])).
% 2.03/0.63  fof(f30,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.03/0.63    inference(ennf_transformation,[],[f14])).
% 2.03/0.63  fof(f14,axiom,(
% 2.03/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.03/0.63  fof(f497,plain,(
% 2.03/0.63    ~spl4_10 | spl4_57 | ~spl4_54),
% 2.03/0.63    inference(avatar_split_clause,[],[f489,f471,f493,f157])).
% 2.03/0.63  fof(f489,plain,(
% 2.03/0.63    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_54),
% 2.03/0.63    inference(superposition,[],[f61,f473])).
% 2.03/0.63  fof(f61,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f25])).
% 2.03/0.63  fof(f25,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.63    inference(ennf_transformation,[],[f7])).
% 2.03/0.63  fof(f7,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.03/0.63  fof(f485,plain,(
% 2.03/0.63    spl4_55),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f484])).
% 2.03/0.63  fof(f484,plain,(
% 2.03/0.63    $false | spl4_55),
% 2.03/0.63    inference(subsumption_resolution,[],[f39,f477])).
% 2.03/0.63  fof(f477,plain,(
% 2.03/0.63    ~v1_funct_2(sK3,sK1,sK0) | spl4_55),
% 2.03/0.63    inference(avatar_component_clause,[],[f475])).
% 2.03/0.63  fof(f39,plain,(
% 2.03/0.63    v1_funct_2(sK3,sK1,sK0)),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f478,plain,(
% 2.03/0.63    spl4_54 | ~spl4_11 | ~spl4_5 | ~spl4_27 | ~spl4_9 | ~spl4_10 | ~spl4_55),
% 2.03/0.63    inference(avatar_split_clause,[],[f466,f475,f157,f153,f282,f119,f161,f471])).
% 2.03/0.63  fof(f466,plain,(
% 2.03/0.63    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.03/0.63    inference(resolution,[],[f64,f42])).
% 2.03/0.63  fof(f42,plain,(
% 2.03/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f64,plain,(
% 2.03/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f29])).
% 2.03/0.63  fof(f29,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.03/0.63    inference(flattening,[],[f28])).
% 2.03/0.63  fof(f28,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.03/0.63    inference(ennf_transformation,[],[f13])).
% 2.03/0.63  fof(f13,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.03/0.63  fof(f348,plain,(
% 2.03/0.63    ~spl4_25),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f336])).
% 2.03/0.63  fof(f336,plain,(
% 2.03/0.63    $false | ~spl4_25),
% 2.03/0.63    inference(subsumption_resolution,[],[f45,f276])).
% 2.03/0.63  fof(f276,plain,(
% 2.03/0.63    k1_xboole_0 = sK1 | ~spl4_25),
% 2.03/0.63    inference(avatar_component_clause,[],[f274])).
% 2.03/0.63  fof(f274,plain,(
% 2.03/0.63    spl4_25 <=> k1_xboole_0 = sK1),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.03/0.63  fof(f45,plain,(
% 2.03/0.63    k1_xboole_0 != sK1),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f300,plain,(
% 2.03/0.63    ~spl4_3 | ~spl4_26 | ~spl4_9 | spl4_28 | ~spl4_24),
% 2.03/0.63    inference(avatar_split_clause,[],[f299,f270,f295,f153,f278,f97])).
% 2.03/0.63  fof(f97,plain,(
% 2.03/0.63    spl4_3 <=> v1_relat_1(sK2)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.03/0.63  fof(f278,plain,(
% 2.03/0.63    spl4_26 <=> v2_funct_1(sK2)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.03/0.63  fof(f270,plain,(
% 2.03/0.63    spl4_24 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.03/0.63  fof(f299,plain,(
% 2.03/0.63    sK0 = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_24),
% 2.03/0.63    inference(forward_demodulation,[],[f291,f78])).
% 2.03/0.63  fof(f291,plain,(
% 2.03/0.63    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_24),
% 2.03/0.63    inference(superposition,[],[f57,f272])).
% 2.03/0.63  fof(f272,plain,(
% 2.03/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_24),
% 2.03/0.63    inference(avatar_component_clause,[],[f270])).
% 2.03/0.63  fof(f289,plain,(
% 2.03/0.63    spl4_27),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f288])).
% 2.03/0.63  fof(f288,plain,(
% 2.03/0.63    $false | spl4_27),
% 2.03/0.63    inference(subsumption_resolution,[],[f48,f284])).
% 2.03/0.63  fof(f284,plain,(
% 2.03/0.63    ~v1_funct_2(sK2,sK0,sK1) | spl4_27),
% 2.03/0.63    inference(avatar_component_clause,[],[f282])).
% 2.03/0.63  fof(f48,plain,(
% 2.03/0.63    v1_funct_2(sK2,sK0,sK1)),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f287,plain,(
% 2.03/0.63    spl4_26),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f286])).
% 2.03/0.63  fof(f286,plain,(
% 2.03/0.63    $false | spl4_26),
% 2.03/0.63    inference(subsumption_resolution,[],[f43,f280])).
% 2.03/0.63  fof(f280,plain,(
% 2.03/0.63    ~v2_funct_1(sK2) | spl4_26),
% 2.03/0.63    inference(avatar_component_clause,[],[f278])).
% 2.03/0.63  fof(f285,plain,(
% 2.03/0.63    spl4_24 | spl4_25 | ~spl4_26 | ~spl4_9 | ~spl4_5 | ~spl4_27),
% 2.03/0.63    inference(avatar_split_clause,[],[f268,f282,f119,f153,f278,f274,f270])).
% 2.03/0.63  fof(f268,plain,(
% 2.03/0.63    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.03/0.63    inference(trivial_inequality_removal,[],[f265])).
% 2.03/0.63  fof(f265,plain,(
% 2.03/0.63    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.03/0.63    inference(superposition,[],[f62,f41])).
% 2.03/0.63  fof(f258,plain,(
% 2.03/0.63    spl4_20 | ~spl4_1 | ~spl4_21 | ~spl4_9 | ~spl4_3 | ~spl4_11 | ~spl4_22 | ~spl4_23 | ~spl4_6 | ~spl4_14),
% 2.03/0.63    inference(avatar_split_clause,[],[f241,f186,f123,f255,f251,f161,f97,f153,f247,f88,f243])).
% 2.03/0.63  fof(f186,plain,(
% 2.03/0.63    spl4_14 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.03/0.63  fof(f241,plain,(
% 2.03/0.63    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_14)),
% 2.03/0.63    inference(forward_demodulation,[],[f240,f125])).
% 2.03/0.63  fof(f240,plain,(
% 2.03/0.63    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_14),
% 2.03/0.63    inference(superposition,[],[f79,f188])).
% 2.03/0.63  fof(f188,plain,(
% 2.03/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_14),
% 2.03/0.63    inference(avatar_component_clause,[],[f186])).
% 2.03/0.63  fof(f232,plain,(
% 2.03/0.63    ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_5 | spl4_14 | ~spl4_8),
% 2.03/0.63    inference(avatar_split_clause,[],[f229,f144,f186,f119,f161,f157,f153])).
% 2.03/0.63  fof(f229,plain,(
% 2.03/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_8),
% 2.03/0.63    inference(superposition,[],[f71,f146])).
% 2.03/0.63  fof(f71,plain,(
% 2.03/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f35])).
% 2.03/0.63  fof(f35,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/0.63    inference(flattening,[],[f34])).
% 2.03/0.63  fof(f34,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/0.63    inference(ennf_transformation,[],[f11])).
% 2.03/0.63  fof(f11,axiom,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.03/0.63  fof(f225,plain,(
% 2.03/0.63    spl4_7),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f214])).
% 2.03/0.63  fof(f214,plain,(
% 2.03/0.63    $false | spl4_7),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f142,f73])).
% 2.03/0.63  fof(f73,plain,(
% 2.03/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f37])).
% 2.03/0.63  fof(f37,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/0.63    inference(flattening,[],[f36])).
% 2.03/0.63  fof(f36,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/0.63    inference(ennf_transformation,[],[f10])).
% 2.03/0.63  fof(f10,axiom,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.03/0.63  fof(f142,plain,(
% 2.03/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 2.03/0.63    inference(avatar_component_clause,[],[f140])).
% 2.03/0.63  fof(f140,plain,(
% 2.03/0.63    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.03/0.63  fof(f40,plain,(
% 2.03/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f38,plain,(
% 2.03/0.63    v1_funct_1(sK3)),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f179,plain,(
% 2.03/0.63    spl4_11),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f178])).
% 2.03/0.63  fof(f178,plain,(
% 2.03/0.63    $false | spl4_11),
% 2.03/0.63    inference(subsumption_resolution,[],[f38,f163])).
% 2.03/0.63  fof(f163,plain,(
% 2.03/0.63    ~v1_funct_1(sK3) | spl4_11),
% 2.03/0.63    inference(avatar_component_clause,[],[f161])).
% 2.03/0.63  fof(f177,plain,(
% 2.03/0.63    spl4_10),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f176])).
% 2.03/0.63  fof(f176,plain,(
% 2.03/0.63    $false | spl4_10),
% 2.03/0.63    inference(subsumption_resolution,[],[f40,f159])).
% 2.03/0.63  fof(f159,plain,(
% 2.03/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_10),
% 2.03/0.63    inference(avatar_component_clause,[],[f157])).
% 2.03/0.63  fof(f175,plain,(
% 2.03/0.63    spl4_9),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f174])).
% 2.03/0.63  fof(f174,plain,(
% 2.03/0.63    $false | spl4_9),
% 2.03/0.63    inference(subsumption_resolution,[],[f47,f155])).
% 2.03/0.63  fof(f155,plain,(
% 2.03/0.63    ~v1_funct_1(sK2) | spl4_9),
% 2.03/0.63    inference(avatar_component_clause,[],[f153])).
% 2.03/0.63  fof(f147,plain,(
% 2.03/0.63    ~spl4_7 | spl4_8),
% 2.03/0.63    inference(avatar_split_clause,[],[f137,f144,f140])).
% 2.03/0.63  fof(f137,plain,(
% 2.03/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.63    inference(resolution,[],[f133,f42])).
% 2.03/0.63  fof(f133,plain,(
% 2.03/0.63    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.03/0.63    inference(resolution,[],[f70,f74])).
% 2.03/0.63  fof(f74,plain,(
% 2.03/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/0.63    inference(definition_unfolding,[],[f51,f50])).
% 2.03/0.63  fof(f51,plain,(
% 2.03/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f9])).
% 2.03/0.63  fof(f9,axiom,(
% 2.03/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.03/0.63  fof(f70,plain,(
% 2.03/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f33])).
% 2.03/0.63  fof(f33,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.63    inference(flattening,[],[f32])).
% 2.03/0.63  fof(f32,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.03/0.63    inference(ennf_transformation,[],[f8])).
% 2.03/0.63  fof(f8,axiom,(
% 2.03/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.03/0.63  fof(f129,plain,(
% 2.03/0.63    spl4_5),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f128])).
% 2.03/0.63  fof(f128,plain,(
% 2.03/0.63    $false | spl4_5),
% 2.03/0.63    inference(subsumption_resolution,[],[f49,f121])).
% 2.03/0.63  fof(f121,plain,(
% 2.03/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.03/0.63    inference(avatar_component_clause,[],[f119])).
% 2.03/0.63  fof(f127,plain,(
% 2.03/0.63    ~spl4_5 | spl4_6),
% 2.03/0.63    inference(avatar_split_clause,[],[f117,f123,f119])).
% 2.03/0.63  fof(f117,plain,(
% 2.03/0.63    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.63    inference(superposition,[],[f41,f61])).
% 2.03/0.63  fof(f112,plain,(
% 2.03/0.63    spl4_4),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f109])).
% 2.03/0.63  fof(f109,plain,(
% 2.03/0.63    $false | spl4_4),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f60,f103])).
% 2.03/0.63  fof(f103,plain,(
% 2.03/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.03/0.63    inference(avatar_component_clause,[],[f101])).
% 2.03/0.63  fof(f101,plain,(
% 2.03/0.63    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.03/0.63  fof(f108,plain,(
% 2.03/0.63    spl4_2),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f105])).
% 2.03/0.63  fof(f105,plain,(
% 2.03/0.63    $false | spl4_2),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f60,f94])).
% 2.03/0.63  fof(f94,plain,(
% 2.03/0.63    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.03/0.63    inference(avatar_component_clause,[],[f92])).
% 2.03/0.63  fof(f92,plain,(
% 2.03/0.63    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.03/0.63  fof(f104,plain,(
% 2.03/0.63    spl4_3 | ~spl4_4),
% 2.03/0.63    inference(avatar_split_clause,[],[f85,f101,f97])).
% 2.03/0.63  fof(f85,plain,(
% 2.03/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.03/0.63    inference(resolution,[],[f56,f49])).
% 2.03/0.63  fof(f95,plain,(
% 2.03/0.63    spl4_1 | ~spl4_2),
% 2.03/0.63    inference(avatar_split_clause,[],[f84,f92,f88])).
% 2.03/0.63  fof(f84,plain,(
% 2.03/0.63    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.03/0.63    inference(resolution,[],[f56,f40])).
% 2.03/0.63  % SZS output end Proof for theBenchmark
% 2.03/0.63  % (5255)------------------------------
% 2.03/0.63  % (5255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (5255)Termination reason: Refutation
% 2.03/0.63  
% 2.03/0.63  % (5255)Memory used [KB]: 6780
% 2.03/0.63  % (5255)Time elapsed: 0.193 s
% 2.03/0.63  % (5255)------------------------------
% 2.03/0.63  % (5255)------------------------------
% 2.03/0.64  % (5241)Success in time 0.273 s
%------------------------------------------------------------------------------
