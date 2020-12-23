%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:52 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 352 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   24
%              Number of atoms          :  514 (2397 expanded)
%              Number of equality atoms :  153 ( 775 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f201,f220,f296,f336,f556,f703])).

fof(f703,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f701,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f701,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(equality_resolution,[],[f568])).

fof(f568,plain,
    ( ! [X4] :
        ( k6_partfun1(sK0) != k6_partfun1(X4)
        | ~ r1_tarski(sK0,X4) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f558,f259])).

fof(f259,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f558,plain,
    ( ! [X4] :
        ( k6_partfun1(sK0) != k6_partfun1(X4)
        | ~ r1_tarski(sK0,X4)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f557,f200])).

fof(f200,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl4_4
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f557,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK0,X4)
        | ~ v1_relat_1(sK3)
        | k5_relat_1(sK2,sK3) != k6_partfun1(X4) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f444,f52])).

fof(f52,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f444,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK0,X4)
        | ~ v1_relat_1(sK3)
        | k5_relat_1(sK2,sK3) != k6_partfun1(X4)
        | sK3 = k2_funct_1(sK2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,
    ( ! [X4] :
        ( k6_partfun1(sK1) != k6_partfun1(sK1)
        | ~ r1_tarski(sK0,X4)
        | ~ v1_relat_1(sK3)
        | k5_relat_1(sK2,sK3) != k6_partfun1(X4)
        | sK3 = k2_funct_1(sK2) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(superposition,[],[f337,f120])).

fof(f120,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f117,f113])).

fof(f113,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f111,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f117,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f46,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f337,plain,
    ( ! [X0,X1] :
        ( k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
        | ~ r1_tarski(sK0,X1)
        | ~ v1_relat_1(X0)
        | k6_partfun1(X1) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f222,f321])).

fof(f321,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | k6_partfun1(X1) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f221,f164])).

fof(f164,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | k6_partfun1(X1) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f161,f169])).

fof(f169,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_2
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k6_partfun1(X1) != k5_relat_1(sK2,X0)
      | k2_funct_1(sK2) = X0 ) ),
    inference(superposition,[],[f93,f137])).

fof(f137,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f136,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f135,f49])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f135,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f133,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f125,f54])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f125,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(superposition,[],[f63,f47])).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
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
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f83,f72,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

fof(f556,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f554,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f554,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_5 ),
    inference(resolution,[],[f266,f46])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_5 ),
    inference(resolution,[],[f260,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f260,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f258])).

fof(f336,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl4_1
    | spl4_7 ),
    inference(subsumption_resolution,[],[f334,f164])).

fof(f334,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f332,f53])).

fof(f332,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f322,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f322,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f320])).

fof(f296,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f294,f53])).

fof(f294,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f293,f46])).

fof(f293,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f292,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f292,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f291,f55])).

fof(f291,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f286,f196])).

fof(f196,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_3
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f286,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f74,f188])).

fof(f188,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f184,f53])).

fof(f184,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f122,f55])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(resolution,[],[f46,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_1(X4)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f220,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f218,f78])).

fof(f218,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f171,f55])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f165,f76])).

fof(f165,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f163])).

fof(f201,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f191,f198,f194])).

fof(f191,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f189,f188])).

fof(f189,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f147,f188])).

fof(f147,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f146,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f77,f72])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f146,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f170,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f143,f167,f163])).

fof(f143,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f108,f142])).

fof(f142,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f139,f116])).

fof(f116,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f115,f55])).

fof(f115,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f54,f69])).

fof(f139,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f55,f84])).

fof(f108,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f104,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:51:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.57  % (4373)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.43/0.58  % (4390)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.59  % (4382)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.59  % (4375)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.60  % (4380)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.75/0.60  % (4391)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.75/0.60  % (4376)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.75/0.61  % (4374)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.75/0.62  % (4384)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.75/0.63  % (4394)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.75/0.63  % (4371)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.75/0.64  % (4386)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.75/0.64  % (4377)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.64  % (4400)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.75/0.64  % (4399)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.75/0.65  % (4392)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.75/0.65  % (4396)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.75/0.65  % (4393)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.75/0.65  % (4398)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.75/0.65  % (4397)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.75/0.65  % (4378)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.75/0.65  % (4381)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.75/0.66  % (4372)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.75/0.66  % (4385)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.75/0.66  % (4388)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.75/0.66  % (4383)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.75/0.66  % (4389)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.22/0.67  % (4387)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.22/0.67  % (4387)Refutation not found, incomplete strategy% (4387)------------------------------
% 2.22/0.67  % (4387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (4387)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.67  
% 2.22/0.67  % (4387)Memory used [KB]: 10746
% 2.22/0.67  % (4387)Time elapsed: 0.224 s
% 2.22/0.67  % (4387)------------------------------
% 2.22/0.67  % (4387)------------------------------
% 2.22/0.67  % (4395)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.22/0.68  % (4379)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.22/0.73  % (4398)Refutation found. Thanks to Tanya!
% 2.22/0.73  % SZS status Theorem for theBenchmark
% 2.22/0.73  % SZS output start Proof for theBenchmark
% 2.22/0.73  fof(f704,plain,(
% 2.22/0.73    $false),
% 2.22/0.73    inference(avatar_sat_refutation,[],[f170,f201,f220,f296,f336,f556,f703])).
% 2.22/0.73  fof(f703,plain,(
% 2.22/0.73    ~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 2.22/0.73    inference(avatar_contradiction_clause,[],[f702])).
% 2.22/0.73  fof(f702,plain,(
% 2.22/0.73    $false | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 2.22/0.73    inference(subsumption_resolution,[],[f701,f101])).
% 2.22/0.73  fof(f101,plain,(
% 2.22/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.73    inference(equality_resolution,[],[f85])).
% 2.22/0.73  fof(f85,plain,(
% 2.22/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.22/0.73    inference(cnf_transformation,[],[f1])).
% 2.22/0.73  fof(f1,axiom,(
% 2.22/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.73  fof(f701,plain,(
% 2.22/0.73    ~r1_tarski(sK0,sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 2.22/0.73    inference(equality_resolution,[],[f568])).
% 2.22/0.73  fof(f568,plain,(
% 2.22/0.73    ( ! [X4] : (k6_partfun1(sK0) != k6_partfun1(X4) | ~r1_tarski(sK0,X4)) ) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 2.22/0.73    inference(subsumption_resolution,[],[f558,f259])).
% 2.22/0.73  fof(f259,plain,(
% 2.22/0.73    v1_relat_1(sK3) | ~spl4_5),
% 2.22/0.73    inference(avatar_component_clause,[],[f258])).
% 2.22/0.73  fof(f258,plain,(
% 2.22/0.73    spl4_5 <=> v1_relat_1(sK3)),
% 2.22/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.22/0.73  fof(f558,plain,(
% 2.22/0.73    ( ! [X4] : (k6_partfun1(sK0) != k6_partfun1(X4) | ~r1_tarski(sK0,X4) | ~v1_relat_1(sK3)) ) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_7)),
% 2.22/0.73    inference(forward_demodulation,[],[f557,f200])).
% 2.22/0.73  fof(f200,plain,(
% 2.22/0.73    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_4),
% 2.22/0.73    inference(avatar_component_clause,[],[f198])).
% 2.22/0.73  fof(f198,plain,(
% 2.22/0.73    spl4_4 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.22/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.73  fof(f557,plain,(
% 2.22/0.73    ( ! [X4] : (~r1_tarski(sK0,X4) | ~v1_relat_1(sK3) | k5_relat_1(sK2,sK3) != k6_partfun1(X4)) ) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 2.22/0.73    inference(subsumption_resolution,[],[f444,f52])).
% 2.22/0.73  fof(f52,plain,(
% 2.22/0.73    sK3 != k2_funct_1(sK2)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f21,plain,(
% 2.22/0.73    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.22/0.73    inference(flattening,[],[f20])).
% 2.22/0.73  fof(f20,plain,(
% 2.22/0.73    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.22/0.73    inference(ennf_transformation,[],[f19])).
% 2.22/0.73  fof(f19,negated_conjecture,(
% 2.22/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.22/0.73    inference(negated_conjecture,[],[f18])).
% 2.22/0.73  fof(f18,conjecture,(
% 2.22/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.22/0.73  fof(f444,plain,(
% 2.22/0.73    ( ! [X4] : (~r1_tarski(sK0,X4) | ~v1_relat_1(sK3) | k5_relat_1(sK2,sK3) != k6_partfun1(X4) | sK3 = k2_funct_1(sK2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 2.22/0.73    inference(trivial_inequality_removal,[],[f443])).
% 2.22/0.73  fof(f443,plain,(
% 2.22/0.73    ( ! [X4] : (k6_partfun1(sK1) != k6_partfun1(sK1) | ~r1_tarski(sK0,X4) | ~v1_relat_1(sK3) | k5_relat_1(sK2,sK3) != k6_partfun1(X4) | sK3 = k2_funct_1(sK2)) ) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 2.22/0.73    inference(superposition,[],[f337,f120])).
% 2.22/0.73  fof(f120,plain,(
% 2.22/0.73    sK1 = k1_relat_1(sK3)),
% 2.22/0.73    inference(forward_demodulation,[],[f117,f113])).
% 2.22/0.73  fof(f113,plain,(
% 2.22/0.73    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.22/0.73    inference(subsumption_resolution,[],[f112,f46])).
% 2.22/0.73  fof(f46,plain,(
% 2.22/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f112,plain,(
% 2.22/0.73    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.73    inference(subsumption_resolution,[],[f111,f50])).
% 2.22/0.73  fof(f50,plain,(
% 2.22/0.73    k1_xboole_0 != sK0),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f111,plain,(
% 2.22/0.73    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.73    inference(resolution,[],[f45,f69])).
% 2.22/0.73  fof(f69,plain,(
% 2.22/0.73    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.73    inference(cnf_transformation,[],[f31])).
% 2.22/0.73  fof(f31,plain,(
% 2.22/0.73    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.73    inference(flattening,[],[f30])).
% 2.22/0.73  fof(f30,plain,(
% 2.22/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.73    inference(ennf_transformation,[],[f12])).
% 2.22/0.73  fof(f12,axiom,(
% 2.22/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.22/0.73  fof(f45,plain,(
% 2.22/0.73    v1_funct_2(sK3,sK1,sK0)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f117,plain,(
% 2.22/0.73    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 2.22/0.73    inference(resolution,[],[f46,f84])).
% 2.22/0.73  fof(f84,plain,(
% 2.22/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f43])).
% 2.22/0.73  fof(f43,plain,(
% 2.22/0.73    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.73    inference(ennf_transformation,[],[f9])).
% 2.22/0.73  fof(f9,axiom,(
% 2.22/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.22/0.73  fof(f337,plain,(
% 2.22/0.73    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1) | ~r1_tarski(sK0,X1) | ~v1_relat_1(X0) | k6_partfun1(X1) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 2.22/0.73    inference(subsumption_resolution,[],[f222,f321])).
% 2.22/0.73  fof(f321,plain,(
% 2.22/0.73    v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 2.22/0.73    inference(avatar_component_clause,[],[f320])).
% 2.22/0.73  fof(f320,plain,(
% 2.22/0.73    spl4_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.22/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.22/0.73  fof(f222,plain,(
% 2.22/0.73    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | k6_partfun1(X1) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | (~spl4_1 | ~spl4_2)),
% 2.22/0.73    inference(subsumption_resolution,[],[f221,f164])).
% 2.22/0.73  fof(f164,plain,(
% 2.22/0.73    v1_relat_1(sK2) | ~spl4_1),
% 2.22/0.73    inference(avatar_component_clause,[],[f163])).
% 2.22/0.73  fof(f163,plain,(
% 2.22/0.73    spl4_1 <=> v1_relat_1(sK2)),
% 2.22/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.73  fof(f221,plain,(
% 2.22/0.73    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | k6_partfun1(X1) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | ~spl4_2),
% 2.22/0.73    inference(backward_demodulation,[],[f161,f169])).
% 2.22/0.73  fof(f169,plain,(
% 2.22/0.73    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl4_2),
% 2.22/0.73    inference(avatar_component_clause,[],[f167])).
% 2.22/0.73  fof(f167,plain,(
% 2.22/0.73    spl4_2 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 2.22/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.73  fof(f161,plain,(
% 2.22/0.73    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | ~v1_relat_1(k2_funct_1(sK2)) | k6_partfun1(X1) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) )),
% 2.22/0.73    inference(superposition,[],[f93,f137])).
% 2.22/0.73  fof(f137,plain,(
% 2.22/0.73    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(subsumption_resolution,[],[f136,f51])).
% 2.22/0.73  fof(f51,plain,(
% 2.22/0.73    k1_xboole_0 != sK1),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f136,plain,(
% 2.22/0.73    k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(subsumption_resolution,[],[f135,f49])).
% 2.22/0.73  fof(f49,plain,(
% 2.22/0.73    v2_funct_1(sK2)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f135,plain,(
% 2.22/0.73    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(subsumption_resolution,[],[f134,f53])).
% 2.22/0.73  fof(f53,plain,(
% 2.22/0.73    v1_funct_1(sK2)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f134,plain,(
% 2.22/0.73    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(subsumption_resolution,[],[f133,f55])).
% 2.22/0.73  fof(f55,plain,(
% 2.22/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f133,plain,(
% 2.22/0.73    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(subsumption_resolution,[],[f125,f54])).
% 2.22/0.73  fof(f54,plain,(
% 2.22/0.73    v1_funct_2(sK2,sK0,sK1)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f125,plain,(
% 2.22/0.73    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(trivial_inequality_removal,[],[f124])).
% 2.22/0.73  fof(f124,plain,(
% 2.22/0.73    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 2.22/0.73    inference(superposition,[],[f63,f47])).
% 2.22/0.73  fof(f47,plain,(
% 2.22/0.73    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f63,plain,(
% 2.22/0.73    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f29])).
% 2.22/0.73  fof(f29,plain,(
% 2.22/0.73    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.22/0.73    inference(flattening,[],[f28])).
% 2.22/0.73  fof(f28,plain,(
% 2.22/0.73    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.22/0.73    inference(ennf_transformation,[],[f16])).
% 2.22/0.73  fof(f16,axiom,(
% 2.22/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.22/0.73  fof(f93,plain,(
% 2.22/0.73    ( ! [X2,X0,X3,X1] : (k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X2,X3) != k6_partfun1(X0) | X1 = X3) )),
% 2.22/0.73    inference(definition_unfolding,[],[f83,f72,f72])).
% 2.22/0.73  fof(f72,plain,(
% 2.22/0.73    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f15])).
% 2.22/0.73  fof(f15,axiom,(
% 2.22/0.73    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.22/0.73  fof(f83,plain,(
% 2.22/0.73    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k6_relat_1(X0) != k5_relat_1(X2,X3) | X1 = X3) )),
% 2.22/0.73    inference(cnf_transformation,[],[f42])).
% 2.22/0.73  fof(f42,plain,(
% 2.22/0.73    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.22/0.73    inference(flattening,[],[f41])).
% 2.22/0.73  fof(f41,plain,(
% 2.22/0.73    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~r1_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.22/0.73    inference(ennf_transformation,[],[f5])).
% 2.22/0.73  fof(f5,axiom,(
% 2.22/0.73    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).
% 2.22/0.73  fof(f556,plain,(
% 2.22/0.73    spl4_5),
% 2.22/0.73    inference(avatar_contradiction_clause,[],[f555])).
% 2.22/0.73  fof(f555,plain,(
% 2.22/0.73    $false | spl4_5),
% 2.22/0.73    inference(subsumption_resolution,[],[f554,f78])).
% 2.22/0.73  fof(f78,plain,(
% 2.22/0.73    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.22/0.73    inference(cnf_transformation,[],[f3])).
% 2.22/0.73  fof(f3,axiom,(
% 2.22/0.73    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.22/0.73  fof(f554,plain,(
% 2.22/0.73    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_5),
% 2.22/0.73    inference(resolution,[],[f266,f46])).
% 2.22/0.73  fof(f266,plain,(
% 2.22/0.73    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_5),
% 2.22/0.73    inference(resolution,[],[f260,f76])).
% 2.22/0.73  fof(f76,plain,(
% 2.22/0.73    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f38])).
% 2.22/0.73  fof(f38,plain,(
% 2.22/0.73    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.73    inference(ennf_transformation,[],[f2])).
% 2.22/0.73  fof(f2,axiom,(
% 2.22/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.22/0.73  fof(f260,plain,(
% 2.22/0.73    ~v1_relat_1(sK3) | spl4_5),
% 2.22/0.73    inference(avatar_component_clause,[],[f258])).
% 2.22/0.73  fof(f336,plain,(
% 2.22/0.73    ~spl4_1 | spl4_7),
% 2.22/0.73    inference(avatar_contradiction_clause,[],[f335])).
% 2.22/0.73  fof(f335,plain,(
% 2.22/0.73    $false | (~spl4_1 | spl4_7)),
% 2.22/0.73    inference(subsumption_resolution,[],[f334,f164])).
% 2.22/0.73  fof(f334,plain,(
% 2.22/0.73    ~v1_relat_1(sK2) | spl4_7),
% 2.22/0.73    inference(subsumption_resolution,[],[f332,f53])).
% 2.22/0.73  fof(f332,plain,(
% 2.22/0.73    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_7),
% 2.22/0.73    inference(resolution,[],[f322,f60])).
% 2.22/0.73  fof(f60,plain,(
% 2.22/0.73    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f27])).
% 2.22/0.73  fof(f27,plain,(
% 2.22/0.73    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.73    inference(flattening,[],[f26])).
% 2.22/0.73  fof(f26,plain,(
% 2.22/0.73    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.73    inference(ennf_transformation,[],[f6])).
% 2.22/0.73  fof(f6,axiom,(
% 2.22/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.22/0.73  fof(f322,plain,(
% 2.22/0.73    ~v1_relat_1(k2_funct_1(sK2)) | spl4_7),
% 2.22/0.73    inference(avatar_component_clause,[],[f320])).
% 2.22/0.73  fof(f296,plain,(
% 2.22/0.73    spl4_3),
% 2.22/0.73    inference(avatar_contradiction_clause,[],[f295])).
% 2.22/0.73  fof(f295,plain,(
% 2.22/0.73    $false | spl4_3),
% 2.22/0.73    inference(subsumption_resolution,[],[f294,f53])).
% 2.22/0.73  fof(f294,plain,(
% 2.22/0.73    ~v1_funct_1(sK2) | spl4_3),
% 2.22/0.73    inference(subsumption_resolution,[],[f293,f46])).
% 2.22/0.73  fof(f293,plain,(
% 2.22/0.73    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_3),
% 2.22/0.73    inference(subsumption_resolution,[],[f292,f44])).
% 2.22/0.73  fof(f44,plain,(
% 2.22/0.73    v1_funct_1(sK3)),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f292,plain,(
% 2.22/0.73    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_3),
% 2.22/0.73    inference(subsumption_resolution,[],[f291,f55])).
% 2.22/0.73  fof(f291,plain,(
% 2.22/0.73    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_3),
% 2.22/0.73    inference(subsumption_resolution,[],[f286,f196])).
% 2.22/0.73  fof(f196,plain,(
% 2.22/0.73    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_3),
% 2.22/0.73    inference(avatar_component_clause,[],[f194])).
% 2.22/0.73  fof(f194,plain,(
% 2.22/0.73    spl4_3 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.73  fof(f286,plain,(
% 2.22/0.73    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 2.22/0.73    inference(superposition,[],[f74,f188])).
% 2.22/0.73  fof(f188,plain,(
% 2.22/0.73    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.22/0.73    inference(subsumption_resolution,[],[f184,f53])).
% 2.22/0.73  fof(f184,plain,(
% 2.22/0.73    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.22/0.73    inference(resolution,[],[f122,f55])).
% 2.22/0.73  fof(f122,plain,(
% 2.22/0.73    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 2.22/0.73    inference(subsumption_resolution,[],[f119,f44])).
% 2.22/0.73  fof(f119,plain,(
% 2.22/0.73    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK3) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 2.22/0.73    inference(resolution,[],[f46,f75])).
% 2.22/0.73  fof(f75,plain,(
% 2.22/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_1(X4) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f37])).
% 2.22/0.73  fof(f37,plain,(
% 2.22/0.73    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.73    inference(flattening,[],[f36])).
% 2.22/0.73  fof(f36,plain,(
% 2.22/0.73    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.73    inference(ennf_transformation,[],[f14])).
% 2.22/0.73  fof(f14,axiom,(
% 2.22/0.73    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.22/0.73  fof(f74,plain,(
% 2.22/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.22/0.73    inference(cnf_transformation,[],[f35])).
% 2.22/0.73  fof(f35,plain,(
% 2.22/0.73    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.73    inference(flattening,[],[f34])).
% 2.22/0.73  fof(f34,plain,(
% 2.22/0.73    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.73    inference(ennf_transformation,[],[f13])).
% 2.22/0.73  fof(f13,axiom,(
% 2.22/0.73    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.22/0.73  fof(f220,plain,(
% 2.22/0.73    spl4_1),
% 2.22/0.73    inference(avatar_contradiction_clause,[],[f219])).
% 2.22/0.73  fof(f219,plain,(
% 2.22/0.73    $false | spl4_1),
% 2.22/0.73    inference(subsumption_resolution,[],[f218,f78])).
% 2.22/0.73  fof(f218,plain,(
% 2.22/0.73    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 2.22/0.73    inference(resolution,[],[f171,f55])).
% 2.22/0.73  fof(f171,plain,(
% 2.22/0.73    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 2.22/0.73    inference(resolution,[],[f165,f76])).
% 2.22/0.73  fof(f165,plain,(
% 2.22/0.73    ~v1_relat_1(sK2) | spl4_1),
% 2.22/0.73    inference(avatar_component_clause,[],[f163])).
% 2.22/0.73  fof(f201,plain,(
% 2.22/0.73    ~spl4_3 | spl4_4),
% 2.22/0.73    inference(avatar_split_clause,[],[f191,f198,f194])).
% 2.22/0.73  fof(f191,plain,(
% 2.22/0.73    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.73    inference(forward_demodulation,[],[f189,f188])).
% 2.22/0.73  fof(f189,plain,(
% 2.22/0.73    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.22/0.73    inference(backward_demodulation,[],[f147,f188])).
% 2.22/0.73  fof(f147,plain,(
% 2.22/0.73    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.73    inference(subsumption_resolution,[],[f146,f90])).
% 2.22/0.73  fof(f90,plain,(
% 2.22/0.73    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.73    inference(definition_unfolding,[],[f77,f72])).
% 2.22/0.73  fof(f77,plain,(
% 2.22/0.73    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.73    inference(cnf_transformation,[],[f11])).
% 2.22/0.73  fof(f11,axiom,(
% 2.22/0.73    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.22/0.73  fof(f146,plain,(
% 2.22/0.73    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.73    inference(resolution,[],[f48,f71])).
% 2.22/0.73  fof(f71,plain,(
% 2.22/0.73    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.73    inference(cnf_transformation,[],[f33])).
% 2.22/0.73  fof(f33,plain,(
% 2.22/0.73    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.73    inference(flattening,[],[f32])).
% 2.22/0.73  fof(f32,plain,(
% 2.22/0.73    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.22/0.73    inference(ennf_transformation,[],[f10])).
% 2.22/0.73  fof(f10,axiom,(
% 2.22/0.73    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.22/0.73  fof(f48,plain,(
% 2.22/0.73    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.73    inference(cnf_transformation,[],[f21])).
% 2.22/0.73  fof(f170,plain,(
% 2.22/0.73    ~spl4_1 | spl4_2),
% 2.22/0.73    inference(avatar_split_clause,[],[f143,f167,f163])).
% 2.22/0.73  fof(f143,plain,(
% 2.22/0.73    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.22/0.73    inference(backward_demodulation,[],[f108,f142])).
% 2.22/0.73  fof(f142,plain,(
% 2.22/0.73    sK0 = k1_relat_1(sK2)),
% 2.22/0.73    inference(forward_demodulation,[],[f139,f116])).
% 2.22/0.73  fof(f116,plain,(
% 2.22/0.73    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.22/0.73    inference(subsumption_resolution,[],[f115,f55])).
% 2.22/0.73  fof(f115,plain,(
% 2.22/0.73    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.73    inference(subsumption_resolution,[],[f114,f51])).
% 2.22/0.73  fof(f114,plain,(
% 2.22/0.73    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.73    inference(resolution,[],[f54,f69])).
% 2.22/0.73  fof(f139,plain,(
% 2.22/0.73    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 2.22/0.73    inference(resolution,[],[f55,f84])).
% 2.22/0.73  fof(f108,plain,(
% 2.22/0.73    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.22/0.73    inference(subsumption_resolution,[],[f104,f53])).
% 2.22/0.73  fof(f104,plain,(
% 2.22/0.73    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.22/0.73    inference(resolution,[],[f49,f59])).
% 2.22/0.73  fof(f59,plain,(
% 2.22/0.73    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 2.22/0.73    inference(cnf_transformation,[],[f25])).
% 2.22/0.73  fof(f25,plain,(
% 2.22/0.73    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.73    inference(flattening,[],[f24])).
% 2.22/0.73  fof(f24,plain,(
% 2.22/0.73    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.73    inference(ennf_transformation,[],[f7])).
% 2.22/0.73  fof(f7,axiom,(
% 2.22/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.22/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.22/0.73  % SZS output end Proof for theBenchmark
% 2.22/0.73  % (4398)------------------------------
% 2.22/0.73  % (4398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.73  % (4398)Termination reason: Refutation
% 2.22/0.73  
% 2.22/0.73  % (4398)Memory used [KB]: 6908
% 2.22/0.73  % (4398)Time elapsed: 0.230 s
% 2.22/0.73  % (4398)------------------------------
% 2.22/0.73  % (4398)------------------------------
% 2.22/0.73  % (4370)Success in time 0.355 s
%------------------------------------------------------------------------------
