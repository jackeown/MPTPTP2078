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
% DateTime   : Thu Dec  3 13:03:03 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 497 expanded)
%              Number of leaves         :   23 ( 102 expanded)
%              Depth                    :   23
%              Number of atoms          :  681 (3595 expanded)
%              Number of equality atoms :  187 (1146 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f509,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f164,f182,f213,f227,f259,f494,f508])).

% (27199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f508,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f506,f324])).

fof(f324,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f323,f49])).

fof(f49,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f323,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f322,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f322,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f321,f180])).

fof(f180,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f321,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f320])).

fof(f320,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(superposition,[],[f166,f212])).

fof(f212,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_7
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f166,plain,
    ( ! [X0] :
        ( k6_partfun1(sK0) != k5_relat_1(sK2,X0)
        | k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f165,f141])).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f165,plain,
    ( ! [X0] :
        ( k6_partfun1(sK0) != k5_relat_1(sK2,X0)
        | k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f136,f146])).

fof(f146,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_2
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f136,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
      | k2_funct_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f135,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
      | k2_funct_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
      | k2_funct_1(sK2) = X0 ) ),
    inference(superposition,[],[f78,f121])).

fof(f121,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f118,f44])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
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
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f506,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f505,f84])).

% (27219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f68])).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f505,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f173,f497])).

fof(f497,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f156,f176])).

fof(f176,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_4
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f156,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f155,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,
    ( ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f154,f41])).

fof(f154,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f153,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f153,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f152,f42])).

fof(f42,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f152,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[],[f53,f132])).

fof(f132,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f131,f41])).

fof(f131,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f130,f52])).

fof(f130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f129,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f129,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f128,f50])).

fof(f128,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f127,f43])).

fof(f127,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f45,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f45,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f173,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_3
  <=> k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f494,plain,
    ( spl4_4
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f492,f80])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f64,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f492,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f491,f267])).

fof(f267,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f200,f212])).

fof(f200,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f198,f50])).

fof(f198,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f99,f52])).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(resolution,[],[f43,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_1(X4)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f491,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f490,f47])).

fof(f490,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_4 ),
    inference(subsumption_resolution,[],[f489,f43])).

fof(f489,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_4 ),
    inference(resolution,[],[f335,f42])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | k1_xboole_0 = X0 )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f334,f50])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f333,f51])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f332,f52])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f329])).

fof(f329,plain,
    ( ! [X0] :
        ( sK1 != sK1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(superposition,[],[f186,f44])).

fof(f186,plain,
    ( ! [X6,X4,X7,X5] :
        ( k2_relset_1(X5,X6,X4) != X6
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(sK3,X6,X7)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3))
        | ~ v1_funct_2(X4,X5,X6)
        | k1_xboole_0 = X7
        | ~ v1_funct_1(X4) )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f184,f41])).

fof(f184,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(X4,X5,X6)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,X6,X7)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3))
        | k2_relset_1(X5,X6,X4) != X6
        | k1_xboole_0 = X7
        | ~ v1_funct_1(X4) )
    | spl4_4 ),
    inference(resolution,[],[f177,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f177,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f259,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f257,f50])).

fof(f257,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f256,f43])).

fof(f256,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f255,f41])).

fof(f255,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f254,f52])).

fof(f254,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f249,f208])).

fof(f208,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl4_6
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f249,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f70,f200])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f227,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f225,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f225,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_5 ),
    inference(resolution,[],[f187,f43])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_5 ),
    inference(resolution,[],[f181,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f181,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f213,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f203,f210,f206])).

fof(f203,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f201,f200])).

fof(f201,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f126,f200])).

fof(f126,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f124,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f74,f68])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f124,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f182,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f89,f179,f175,f171])).

fof(f89,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

% (27206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f164,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f162,f75])).

fof(f162,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f148,f52])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f142,f73])).

fof(f142,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f147,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f111,f144,f140])).

fof(f111,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f109,f83])).

fof(f83,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f68])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f109,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f94,f108])).

fof(f108,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f107,f48])).

fof(f48,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f105,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f104,f52])).

fof(f104,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f53,f44])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:03:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.50  % (27218)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.50  % (27210)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.50  % (27202)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.52  % (27210)Refutation not found, incomplete strategy% (27210)------------------------------
% 0.19/0.52  % (27210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (27210)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (27210)Memory used [KB]: 10746
% 0.19/0.52  % (27210)Time elapsed: 0.126 s
% 0.19/0.52  % (27210)------------------------------
% 0.19/0.52  % (27210)------------------------------
% 0.19/0.52  % (27221)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.52  % (27197)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (27194)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (27198)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (27208)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.53  % (27195)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (27200)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (27222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.54  % (27212)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.54  % (27203)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.54  % (27214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (27204)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.55  % (27220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (27196)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.55  % (27213)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.56  % (27209)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.56  % (27216)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.56  % (27205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.56  % (27217)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.56  % (27201)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.56  % (27222)Refutation not found, incomplete strategy% (27222)------------------------------
% 0.19/0.56  % (27222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (27221)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f509,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f147,f164,f182,f213,f227,f259,f494,f508])).
% 0.19/0.56  % (27199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.56  fof(f508,plain,(
% 0.19/0.56    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f507])).
% 0.19/0.56  fof(f507,plain,(
% 0.19/0.56    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.19/0.56    inference(subsumption_resolution,[],[f506,f324])).
% 0.19/0.56  fof(f324,plain,(
% 0.19/0.56    sK1 != k1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_7)),
% 0.19/0.56    inference(subsumption_resolution,[],[f323,f49])).
% 0.19/0.56  fof(f49,plain,(
% 0.19/0.56    sK3 != k2_funct_1(sK2)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.56    inference(flattening,[],[f19])).
% 0.19/0.56  fof(f19,plain,(
% 0.19/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.56    inference(ennf_transformation,[],[f18])).
% 0.19/0.56  fof(f18,negated_conjecture,(
% 0.19/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.19/0.56    inference(negated_conjecture,[],[f17])).
% 0.19/0.56  fof(f17,conjecture,(
% 0.19/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.19/0.56  fof(f323,plain,(
% 0.19/0.56    sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_7)),
% 0.19/0.56    inference(subsumption_resolution,[],[f322,f41])).
% 0.19/0.56  fof(f41,plain,(
% 0.19/0.56    v1_funct_1(sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f322,plain,(
% 0.19/0.56    sK1 != k1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_7)),
% 0.19/0.56    inference(subsumption_resolution,[],[f321,f180])).
% 0.19/0.56  fof(f180,plain,(
% 0.19/0.56    v1_relat_1(sK3) | ~spl4_5),
% 0.19/0.56    inference(avatar_component_clause,[],[f179])).
% 0.19/0.56  fof(f179,plain,(
% 0.19/0.56    spl4_5 <=> v1_relat_1(sK3)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.56  fof(f321,plain,(
% 0.19/0.56    sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 0.19/0.56    inference(trivial_inequality_removal,[],[f320])).
% 0.19/0.56  fof(f320,plain,(
% 0.19/0.56    k6_partfun1(sK0) != k6_partfun1(sK0) | sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 0.19/0.56    inference(superposition,[],[f166,f212])).
% 0.19/0.56  fof(f212,plain,(
% 0.19/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_7),
% 0.19/0.56    inference(avatar_component_clause,[],[f210])).
% 0.19/0.56  fof(f210,plain,(
% 0.19/0.56    spl4_7 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.56  fof(f166,plain,(
% 0.19/0.56    ( ! [X0] : (k6_partfun1(sK0) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(sK2) = X0) ) | (~spl4_1 | ~spl4_2)),
% 0.19/0.56    inference(subsumption_resolution,[],[f165,f141])).
% 0.19/0.56  fof(f141,plain,(
% 0.19/0.56    v1_relat_1(sK2) | ~spl4_1),
% 0.19/0.56    inference(avatar_component_clause,[],[f140])).
% 0.19/0.56  fof(f140,plain,(
% 0.19/0.56    spl4_1 <=> v1_relat_1(sK2)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.56  fof(f165,plain,(
% 0.19/0.56    ( ! [X0] : (k6_partfun1(sK0) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = X0) ) | ~spl4_2),
% 0.19/0.56    inference(backward_demodulation,[],[f136,f146])).
% 0.19/0.56  fof(f146,plain,(
% 0.19/0.56    sK0 = k1_relat_1(sK2) | ~spl4_2),
% 0.19/0.56    inference(avatar_component_clause,[],[f144])).
% 0.19/0.56  fof(f144,plain,(
% 0.19/0.56    spl4_2 <=> sK0 = k1_relat_1(sK2)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.56  fof(f136,plain,(
% 0.19/0.56    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = X0) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f135,f46])).
% 0.19/0.56  fof(f46,plain,(
% 0.19/0.56    v2_funct_1(sK2)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f135,plain,(
% 0.19/0.56    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = X0) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f134,f50])).
% 0.19/0.56  fof(f50,plain,(
% 0.19/0.56    v1_funct_1(sK2)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f134,plain,(
% 0.19/0.56    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(sK2) = X0) )),
% 0.19/0.56    inference(superposition,[],[f78,f121])).
% 0.19/0.56  fof(f121,plain,(
% 0.19/0.56    sK1 = k2_relat_1(sK2)),
% 0.19/0.56    inference(forward_demodulation,[],[f118,f44])).
% 0.19/0.56  fof(f44,plain,(
% 0.19/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f118,plain,(
% 0.19/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.19/0.56    inference(resolution,[],[f52,f72])).
% 0.19/0.56  fof(f72,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f39])).
% 0.19/0.56  fof(f39,plain,(
% 0.19/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.56    inference(ennf_transformation,[],[f8])).
% 0.19/0.56  fof(f8,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.56  fof(f52,plain,(
% 0.19/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f78,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.19/0.56    inference(definition_unfolding,[],[f55,f68])).
% 0.19/0.56  fof(f68,plain,(
% 0.19/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f13,axiom,(
% 0.19/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.56  fof(f55,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f24])).
% 0.19/0.56  fof(f24,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.56    inference(flattening,[],[f23])).
% 0.19/0.56  fof(f23,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f7])).
% 0.19/0.56  fof(f7,axiom,(
% 0.19/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.19/0.56  fof(f506,plain,(
% 0.19/0.56    sK1 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_4)),
% 0.19/0.56    inference(forward_demodulation,[],[f505,f84])).
% 0.19/0.56  % (27219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.56  fof(f84,plain,(
% 0.19/0.56    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.19/0.56    inference(definition_unfolding,[],[f76,f68])).
% 0.19/0.56  fof(f76,plain,(
% 0.19/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.56    inference(cnf_transformation,[],[f3])).
% 0.19/0.56  fof(f3,axiom,(
% 0.19/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.56  fof(f505,plain,(
% 0.19/0.56    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | (~spl4_3 | ~spl4_4)),
% 0.19/0.56    inference(forward_demodulation,[],[f173,f497])).
% 0.19/0.56  fof(f497,plain,(
% 0.19/0.56    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_4),
% 0.19/0.56    inference(subsumption_resolution,[],[f156,f176])).
% 0.19/0.56  fof(f176,plain,(
% 0.19/0.56    v2_funct_1(sK3) | ~spl4_4),
% 0.19/0.56    inference(avatar_component_clause,[],[f175])).
% 0.19/0.56  fof(f175,plain,(
% 0.19/0.56    spl4_4 <=> v2_funct_1(sK3)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.56  fof(f156,plain,(
% 0.19/0.56    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.19/0.56    inference(subsumption_resolution,[],[f155,f47])).
% 0.19/0.56  fof(f47,plain,(
% 0.19/0.56    k1_xboole_0 != sK0),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f155,plain,(
% 0.19/0.56    ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.19/0.56    inference(subsumption_resolution,[],[f154,f41])).
% 0.19/0.56  fof(f154,plain,(
% 0.19/0.56    ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.19/0.56    inference(subsumption_resolution,[],[f153,f43])).
% 0.19/0.56  fof(f43,plain,(
% 0.19/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f153,plain,(
% 0.19/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.19/0.56    inference(subsumption_resolution,[],[f152,f42])).
% 0.19/0.56  fof(f42,plain,(
% 0.19/0.56    v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f152,plain,(
% 0.19/0.56    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.19/0.56    inference(trivial_inequality_removal,[],[f149])).
% 0.19/0.56  fof(f149,plain,(
% 0.19/0.56    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.19/0.56    inference(superposition,[],[f53,f132])).
% 0.19/0.56  fof(f132,plain,(
% 0.19/0.56    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f131,f41])).
% 0.19/0.56  fof(f131,plain,(
% 0.19/0.56    ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f130,f52])).
% 0.19/0.56  fof(f130,plain,(
% 0.19/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f129,f51])).
% 0.19/0.56  fof(f51,plain,(
% 0.19/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f129,plain,(
% 0.19/0.56    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f128,f50])).
% 0.19/0.56  fof(f128,plain,(
% 0.19/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f127,f43])).
% 0.19/0.57  fof(f127,plain,(
% 0.19/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.57    inference(subsumption_resolution,[],[f125,f42])).
% 0.19/0.57  fof(f125,plain,(
% 0.19/0.57    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.19/0.57    inference(resolution,[],[f45,f67])).
% 0.19/0.57  fof(f67,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f34])).
% 0.19/0.57  fof(f34,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.57    inference(flattening,[],[f33])).
% 0.19/0.57  fof(f33,plain,(
% 0.19/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.57    inference(ennf_transformation,[],[f14])).
% 0.19/0.57  fof(f14,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 0.19/0.57  fof(f45,plain,(
% 0.19/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.19/0.57    inference(cnf_transformation,[],[f20])).
% 0.19/0.57  fof(f53,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f22])).
% 0.19/0.57  fof(f22,plain,(
% 0.19/0.57    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.57    inference(flattening,[],[f21])).
% 0.19/0.57  fof(f21,plain,(
% 0.19/0.57    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.57    inference(ennf_transformation,[],[f16])).
% 0.19/0.57  fof(f16,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.19/0.57  fof(f173,plain,(
% 0.19/0.57    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~spl4_3),
% 0.19/0.57    inference(avatar_component_clause,[],[f171])).
% 0.19/0.57  fof(f171,plain,(
% 0.19/0.57    spl4_3 <=> k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.57  fof(f494,plain,(
% 0.19/0.57    spl4_4 | ~spl4_7),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f493])).
% 0.19/0.57  fof(f493,plain,(
% 0.19/0.57    $false | (spl4_4 | ~spl4_7)),
% 0.19/0.57    inference(subsumption_resolution,[],[f492,f80])).
% 0.19/0.57  fof(f80,plain,(
% 0.19/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.19/0.57    inference(definition_unfolding,[],[f64,f68])).
% 0.19/0.57  fof(f64,plain,(
% 0.19/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f4])).
% 0.19/0.57  fof(f4,axiom,(
% 0.19/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.19/0.57  fof(f492,plain,(
% 0.19/0.57    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_4 | ~spl4_7)),
% 0.19/0.57    inference(forward_demodulation,[],[f491,f267])).
% 0.19/0.57  fof(f267,plain,(
% 0.19/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_7),
% 0.19/0.57    inference(backward_demodulation,[],[f200,f212])).
% 0.19/0.57  fof(f200,plain,(
% 0.19/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.19/0.57    inference(subsumption_resolution,[],[f198,f50])).
% 0.19/0.57  fof(f198,plain,(
% 0.19/0.57    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.19/0.57    inference(resolution,[],[f99,f52])).
% 0.19/0.57  fof(f99,plain,(
% 0.19/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f97,f41])).
% 0.19/0.57  fof(f97,plain,(
% 0.19/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK3) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 0.19/0.57    inference(resolution,[],[f43,f71])).
% 1.69/0.57  fof(f71,plain,(
% 1.69/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_1(X4) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.69/0.57    inference(cnf_transformation,[],[f38])).
% 1.69/0.57  fof(f38,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.57    inference(flattening,[],[f37])).
% 1.69/0.57  fof(f37,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.57    inference(ennf_transformation,[],[f12])).
% 1.69/0.57  fof(f12,axiom,(
% 1.69/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.69/0.57  fof(f491,plain,(
% 1.69/0.57    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_4),
% 1.69/0.57    inference(subsumption_resolution,[],[f490,f47])).
% 1.69/0.57  fof(f490,plain,(
% 1.69/0.57    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | spl4_4),
% 1.69/0.57    inference(subsumption_resolution,[],[f489,f43])).
% 1.69/0.57  fof(f489,plain,(
% 1.69/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | spl4_4),
% 1.69/0.57    inference(resolution,[],[f335,f42])).
% 1.69/0.57  fof(f335,plain,(
% 1.69/0.57    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | k1_xboole_0 = X0) ) | spl4_4),
% 1.69/0.57    inference(subsumption_resolution,[],[f334,f50])).
% 1.69/0.57  fof(f334,plain,(
% 1.69/0.57    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.69/0.57    inference(subsumption_resolution,[],[f333,f51])).
% 1.69/0.57  fof(f333,plain,(
% 1.69/0.57    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.69/0.57    inference(subsumption_resolution,[],[f332,f52])).
% 1.69/0.57  fof(f332,plain,(
% 1.69/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.69/0.57    inference(trivial_inequality_removal,[],[f329])).
% 1.69/0.57  fof(f329,plain,(
% 1.69/0.57    ( ! [X0] : (sK1 != sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.69/0.57    inference(superposition,[],[f186,f44])).
% 1.69/0.57  fof(f186,plain,(
% 1.69/0.57    ( ! [X6,X4,X7,X5] : (k2_relset_1(X5,X6,X4) != X6 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(sK3,X6,X7) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3)) | ~v1_funct_2(X4,X5,X6) | k1_xboole_0 = X7 | ~v1_funct_1(X4)) ) | spl4_4),
% 1.69/0.57    inference(subsumption_resolution,[],[f184,f41])).
% 1.69/0.57  fof(f184,plain,(
% 1.69/0.57    ( ! [X6,X4,X7,X5] : (~v1_funct_2(X4,X5,X6) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,X6,X7) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3)) | k2_relset_1(X5,X6,X4) != X6 | k1_xboole_0 = X7 | ~v1_funct_1(X4)) ) | spl4_4),
% 1.69/0.57    inference(resolution,[],[f177,f61])).
% 1.69/0.57  fof(f61,plain,(
% 1.69/0.57    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.69/0.57    inference(cnf_transformation,[],[f28])).
% 1.69/0.57  fof(f28,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.69/0.57    inference(flattening,[],[f27])).
% 1.69/0.57  fof(f27,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.69/0.57    inference(ennf_transformation,[],[f15])).
% 1.69/0.57  fof(f15,axiom,(
% 1.69/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.69/0.57  fof(f177,plain,(
% 1.69/0.57    ~v2_funct_1(sK3) | spl4_4),
% 1.69/0.57    inference(avatar_component_clause,[],[f175])).
% 1.69/0.57  fof(f259,plain,(
% 1.69/0.57    spl4_6),
% 1.69/0.57    inference(avatar_contradiction_clause,[],[f258])).
% 1.69/0.57  fof(f258,plain,(
% 1.69/0.57    $false | spl4_6),
% 1.69/0.57    inference(subsumption_resolution,[],[f257,f50])).
% 1.69/0.57  fof(f257,plain,(
% 1.69/0.57    ~v1_funct_1(sK2) | spl4_6),
% 1.69/0.57    inference(subsumption_resolution,[],[f256,f43])).
% 1.69/0.57  fof(f256,plain,(
% 1.69/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 1.69/0.57    inference(subsumption_resolution,[],[f255,f41])).
% 1.69/0.57  fof(f255,plain,(
% 1.69/0.57    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 1.69/0.57    inference(subsumption_resolution,[],[f254,f52])).
% 1.69/0.57  fof(f254,plain,(
% 1.69/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 1.69/0.57    inference(subsumption_resolution,[],[f249,f208])).
% 1.69/0.57  fof(f208,plain,(
% 1.69/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_6),
% 1.69/0.57    inference(avatar_component_clause,[],[f206])).
% 1.69/0.57  fof(f206,plain,(
% 1.69/0.57    spl4_6 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.69/0.57  fof(f249,plain,(
% 1.69/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 1.69/0.57    inference(superposition,[],[f70,f200])).
% 1.69/0.57  fof(f70,plain,(
% 1.69/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.69/0.57    inference(cnf_transformation,[],[f36])).
% 1.69/0.57  fof(f36,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.57    inference(flattening,[],[f35])).
% 1.69/0.57  fof(f35,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.57    inference(ennf_transformation,[],[f11])).
% 1.69/0.57  fof(f11,axiom,(
% 1.69/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.69/0.57  fof(f227,plain,(
% 1.69/0.57    spl4_5),
% 1.69/0.57    inference(avatar_contradiction_clause,[],[f226])).
% 1.69/0.57  fof(f226,plain,(
% 1.69/0.57    $false | spl4_5),
% 1.69/0.57    inference(subsumption_resolution,[],[f225,f75])).
% 1.69/0.57  fof(f75,plain,(
% 1.69/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.69/0.57    inference(cnf_transformation,[],[f2])).
% 1.69/0.57  fof(f2,axiom,(
% 1.69/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.69/0.57  fof(f225,plain,(
% 1.69/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_5),
% 1.69/0.57    inference(resolution,[],[f187,f43])).
% 1.69/0.57  fof(f187,plain,(
% 1.69/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_5),
% 1.69/0.57    inference(resolution,[],[f181,f73])).
% 1.69/0.57  fof(f73,plain,(
% 1.69/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.69/0.57    inference(cnf_transformation,[],[f40])).
% 1.69/0.57  fof(f40,plain,(
% 1.69/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.69/0.57    inference(ennf_transformation,[],[f1])).
% 1.69/0.57  fof(f1,axiom,(
% 1.69/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.69/0.57  fof(f181,plain,(
% 1.69/0.57    ~v1_relat_1(sK3) | spl4_5),
% 1.69/0.57    inference(avatar_component_clause,[],[f179])).
% 1.69/0.57  fof(f213,plain,(
% 1.69/0.57    ~spl4_6 | spl4_7),
% 1.69/0.57    inference(avatar_split_clause,[],[f203,f210,f206])).
% 1.69/0.57  fof(f203,plain,(
% 1.69/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.57    inference(forward_demodulation,[],[f201,f200])).
% 1.69/0.57  fof(f201,plain,(
% 1.69/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.69/0.57    inference(backward_demodulation,[],[f126,f200])).
% 1.69/0.57  fof(f126,plain,(
% 1.69/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.57    inference(subsumption_resolution,[],[f124,f82])).
% 1.69/0.57  fof(f82,plain,(
% 1.69/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.69/0.57    inference(definition_unfolding,[],[f74,f68])).
% 1.69/0.57  fof(f74,plain,(
% 1.69/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.69/0.57    inference(cnf_transformation,[],[f10])).
% 1.69/0.57  fof(f10,axiom,(
% 1.69/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.69/0.57  fof(f124,plain,(
% 1.69/0.57    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.57    inference(resolution,[],[f45,f66])).
% 1.69/0.57  fof(f66,plain,(
% 1.69/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.57    inference(cnf_transformation,[],[f32])).
% 1.69/0.57  fof(f32,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.57    inference(flattening,[],[f31])).
% 1.69/0.57  fof(f31,plain,(
% 1.69/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.69/0.57    inference(ennf_transformation,[],[f9])).
% 1.69/0.57  fof(f9,axiom,(
% 1.69/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.69/0.57  fof(f182,plain,(
% 1.69/0.57    spl4_3 | ~spl4_4 | ~spl4_5),
% 1.69/0.57    inference(avatar_split_clause,[],[f89,f179,f175,f171])).
% 1.69/0.57  fof(f89,plain,(
% 1.69/0.57    ~v1_relat_1(sK3) | ~v2_funct_1(sK3) | k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 1.69/0.57    inference(resolution,[],[f41,f56])).
% 1.69/0.57  fof(f56,plain,(
% 1.69/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 1.69/0.57    inference(cnf_transformation,[],[f26])).
% 1.69/0.57  fof(f26,plain,(
% 1.69/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.57    inference(flattening,[],[f25])).
% 1.69/0.57  fof(f25,plain,(
% 1.69/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.57    inference(ennf_transformation,[],[f6])).
% 1.69/0.57  fof(f6,axiom,(
% 1.69/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.69/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.69/0.57  % (27206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.69/0.57  fof(f164,plain,(
% 1.69/0.57    spl4_1),
% 1.69/0.57    inference(avatar_contradiction_clause,[],[f163])).
% 1.69/0.57  fof(f163,plain,(
% 1.69/0.57    $false | spl4_1),
% 1.69/0.57    inference(subsumption_resolution,[],[f162,f75])).
% 1.69/0.57  fof(f162,plain,(
% 1.69/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 1.69/0.57    inference(resolution,[],[f148,f52])).
% 1.69/0.57  fof(f148,plain,(
% 1.69/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 1.69/0.57    inference(resolution,[],[f142,f73])).
% 1.69/0.57  fof(f142,plain,(
% 1.69/0.57    ~v1_relat_1(sK2) | spl4_1),
% 1.69/0.57    inference(avatar_component_clause,[],[f140])).
% 1.69/0.57  fof(f147,plain,(
% 1.69/0.57    ~spl4_1 | spl4_2),
% 1.69/0.57    inference(avatar_split_clause,[],[f111,f144,f140])).
% 1.69/0.57  fof(f111,plain,(
% 1.69/0.57    sK0 = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.57    inference(forward_demodulation,[],[f109,f83])).
% 1.69/0.57  fof(f83,plain,(
% 1.69/0.57    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.69/0.57    inference(definition_unfolding,[],[f77,f68])).
% 1.69/0.57  fof(f77,plain,(
% 1.69/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.57    inference(cnf_transformation,[],[f3])).
% 1.69/0.57  fof(f109,plain,(
% 1.69/0.57    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2)),
% 1.69/0.57    inference(backward_demodulation,[],[f94,f108])).
% 1.69/0.57  fof(f108,plain,(
% 1.69/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(subsumption_resolution,[],[f107,f48])).
% 1.69/0.57  fof(f48,plain,(
% 1.69/0.57    k1_xboole_0 != sK1),
% 1.69/0.57    inference(cnf_transformation,[],[f20])).
% 1.69/0.57  fof(f107,plain,(
% 1.69/0.57    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(subsumption_resolution,[],[f106,f46])).
% 1.69/0.57  fof(f106,plain,(
% 1.69/0.57    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(subsumption_resolution,[],[f105,f50])).
% 1.69/0.57  fof(f105,plain,(
% 1.69/0.57    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(subsumption_resolution,[],[f104,f52])).
% 1.69/0.57  fof(f104,plain,(
% 1.69/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(subsumption_resolution,[],[f103,f51])).
% 1.69/0.57  fof(f103,plain,(
% 1.69/0.57    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(trivial_inequality_removal,[],[f100])).
% 1.69/0.57  fof(f100,plain,(
% 1.69/0.57    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.57    inference(superposition,[],[f53,f44])).
% 1.69/0.57  fof(f94,plain,(
% 1.69/0.57    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.69/0.57    inference(subsumption_resolution,[],[f92,f46])).
% 1.69/0.57  fof(f92,plain,(
% 1.69/0.57    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.69/0.57    inference(resolution,[],[f50,f57])).
% 1.69/0.57  fof(f57,plain,(
% 1.69/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 1.69/0.57    inference(cnf_transformation,[],[f26])).
% 1.69/0.57  % SZS output end Proof for theBenchmark
% 1.69/0.57  % (27221)------------------------------
% 1.69/0.57  % (27221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.57  % (27221)Termination reason: Refutation
% 1.69/0.57  
% 1.69/0.57  % (27221)Memory used [KB]: 6652
% 1.69/0.57  % (27221)Time elapsed: 0.103 s
% 1.69/0.57  % (27221)------------------------------
% 1.69/0.57  % (27221)------------------------------
% 1.69/0.57  % (27193)Success in time 0.223 s
%------------------------------------------------------------------------------
