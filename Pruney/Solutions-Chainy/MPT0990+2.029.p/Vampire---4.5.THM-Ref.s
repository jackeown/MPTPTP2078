%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 723 expanded)
%              Number of leaves         :   18 ( 220 expanded)
%              Depth                    :   31
%              Number of atoms          :  647 (7059 expanded)
%              Number of equality atoms :  193 (2438 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f207,f211,f1235])).

fof(f1235,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f1231,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f1231,plain,
    ( ! [X4,X5] : ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f1230])).

fof(f1230,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1229,f355])).

fof(f355,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK4) ),
    inference(global_subsumption,[],[f349,f354])).

fof(f354,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f338,f154])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f75,f58])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f338,plain,(
    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) ),
    inference(backward_demodulation,[],[f51,f268])).

fof(f268,plain,(
    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f264,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & sK2 = k2_relset_1(sK1,sK2,sK3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( k2_funct_1(sK3) != X3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & v2_funct_1(sK3)
        & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
        & sK2 = k2_relset_1(sK1,sK2,sK3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X3,sK2,sK1)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK3) != sK4
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & v2_funct_1(sK3)
      & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

% (4257)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f264,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f163,f46])).

% (4258)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f160,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f51,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f349,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f348,f44])).

fof(f348,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f347,f46])).

fof(f347,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f346,f47])).

fof(f346,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f340,f49])).

fof(f340,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f79,f268])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1229,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1228,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1228,plain,
    ( ! [X4,X5] :
        ( ~ r2_relset_1(X4,X5,k6_partfun1(sK1),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1227,f355])).

fof(f1227,plain,
    ( ! [X4,X5] :
        ( ~ r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1226,f90])).

fof(f90,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f64,f49])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1226,plain,
    ( ! [X4,X5] :
        ( ~ r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_relat_1(sK4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1225,f47])).

fof(f1225,plain,
    ( ! [X4,X5] :
        ( ~ r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1210,f55])).

fof(f55,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f1210,plain,
    ( ! [X4,X5] :
        ( ~ r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k2_funct_1(sK3) = sK4
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f1209])).

fof(f1209,plain,
    ( ! [X4,X5] :
        ( k6_partfun1(sK2) != k6_partfun1(sK2)
        | ~ r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k2_funct_1(sK3) = sK4
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f648,f137])).

fof(f137,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f105,f128])).

fof(f128,plain,(
    sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f127,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f48,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(resolution,[],[f66,f93])).

fof(f93,plain,(
    sP0(sK2,sK4,sK1) ),
    inference(resolution,[],[f70,f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f105,plain,(
    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f648,plain,
    ( ! [X6,X4,X5] :
        ( k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
        | ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(sK1))
        | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k2_funct_1(sK3) = X4
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f647,f131])).

fof(f131,plain,(
    sK1 = k2_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f103,f130])).

fof(f130,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f104,f126])).

fof(f126,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f125,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f122,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f70,f46])).

fof(f104,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f65,f46])).

fof(f103,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f102,f89])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f64,f46])).

fof(f102,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f101,f44])).

fof(f101,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f647,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(sK1))
        | k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
        | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k2_funct_1(sK3) = X4
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f646,f131])).

fof(f646,plain,
    ( ! [X6,X4,X5] :
        ( k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
        | ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3))))
        | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k2_funct_1(sK3) = X4
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f645,f194])).

fof(f194,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_3
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f645,plain,
    ( ! [X6,X4,X5] :
        ( k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
        | ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3))))
        | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k2_funct_1(sK3) = X4
        | ~ m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(k2_funct_1(sK3)) )
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f644,f198])).

fof(f198,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl5_4
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f644,plain,(
    ! [X6,X4,X5] :
      ( k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
      | ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3))))
      | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k2_funct_1(sK3) = X4
      | ~ m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ v1_relat_1(k2_funct_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f643,f89])).

fof(f643,plain,(
    ! [X6,X4,X5] :
      ( k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
      | ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3))))
      | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k2_funct_1(sK3) = X4
      | ~ m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ v1_relat_1(k2_funct_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f635,f44])).

fof(f635,plain,(
    ! [X6,X4,X5] :
      ( k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2)
      | ~ r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3))))
      | ~ m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k2_funct_1(sK3) = X4
      | ~ m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ v1_relat_1(k2_funct_1(sK3)) ) ),
    inference(superposition,[],[f189,f235])).

fof(f235,plain,(
    k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) ),
    inference(subsumption_resolution,[],[f234,f44])).

fof(f234,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f233,f45])).

fof(f233,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f232,f46])).

fof(f232,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f231,f52])).

fof(f231,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f230,f54])).

fof(f230,plain,
    ( k1_xboole_0 = sK2
    | ~ v2_funct_1(sK3)
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f229])).

fof(f229,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK2
    | ~ v2_funct_1(sK3)
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f74,f50])).

fof(f50,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f189,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_relat_1(X0,X3) != k6_partfun1(k1_relat_1(X4))
      | ~ r2_relset_1(X1,X2,k5_relat_1(X3,X4),k6_partfun1(k2_relat_1(X0)))
      | ~ m1_subset_1(k5_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | X0 = X4
      | ~ m1_subset_1(k6_partfun1(k2_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f75,f81])).

fof(f81,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f56,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).

fof(f211,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f209,f89])).

fof(f209,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f208,f44])).

fof(f208,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_4 ),
    inference(resolution,[],[f199,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f199,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f207,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f205,f89])).

% (4285)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f205,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f204,f44])).

fof(f204,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(resolution,[],[f195,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f195,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n006.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:36:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.44  % (4262)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (4278)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.47  % (4270)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (4261)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (4259)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (4262)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1236,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f207,f211,f1235])).
% 0.21/0.51  fof(f1235,plain,(
% 0.21/0.51    ~spl5_3 | ~spl5_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1234])).
% 0.21/0.51  fof(f1234,plain,(
% 0.21/0.51    $false | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(resolution,[],[f1231,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.51  fof(f1231,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f1230])).
% 0.21/0.51  fof(f1230,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f1229,f355])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    k6_partfun1(sK1) = k5_relat_1(sK3,sK4)),
% 0.21/0.51    inference(global_subsumption,[],[f349,f354])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    k6_partfun1(sK1) = k5_relat_1(sK3,sK4) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.51    inference(resolution,[],[f338,f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.21/0.51    inference(resolution,[],[f75,f58])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1))),
% 0.21/0.51    inference(backward_demodulation,[],[f51,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f264,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f38,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) => (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  % (4257)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f163,f46])).
% 0.21/0.51  % (4258)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4) | ~v1_funct_1(X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f160,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.21/0.51    inference(resolution,[],[f77,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f348,f44])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f347,f46])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f346,f47])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f340,f49])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(superposition,[],[f79,f268])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.51  fof(f1229,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1228,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f1228,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_relset_1(X4,X5,k6_partfun1(sK1),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f1227,f355])).
% 0.21/0.51  fof(f1227,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1226,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    v1_relat_1(sK4)),
% 0.21/0.51    inference(resolution,[],[f64,f49])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f1226,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_relat_1(sK4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1225,f47])).
% 0.21/0.51  fof(f1225,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1210,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k2_funct_1(sK3) != sK4),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f1210,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k2_funct_1(sK3) = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f1209])).
% 0.21/0.51  fof(f1209,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k6_partfun1(sK2) != k6_partfun1(sK2) | ~r2_relset_1(X4,X5,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k2_funct_1(sK3) = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(superposition,[],[f648,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    sK2 = k1_relat_1(sK4)),
% 0.21/0.51    inference(backward_demodulation,[],[f105,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    sK2 = k1_relset_1(sK2,sK1,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f123,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~v1_funct_2(sK4,sK2,sK1) | k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 0.21/0.51    inference(resolution,[],[f66,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    sP0(sK2,sK4,sK1)),
% 0.21/0.51    inference(resolution,[],[f70,f49])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(definition_folding,[],[f26,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f35])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4)),
% 0.21/0.51    inference(resolution,[],[f65,f49])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f648,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(sK1)) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f647,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    sK1 = k2_relat_1(k2_funct_1(sK3))),
% 0.21/0.51    inference(backward_demodulation,[],[f103,f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    sK1 = k1_relat_1(sK3)),
% 0.21/0.51    inference(backward_demodulation,[],[f104,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f66,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    sP0(sK1,sK3,sK2)),
% 0.21/0.51    inference(resolution,[],[f70,f46])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f65,f46])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f64,f46])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f44])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f62,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v2_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f647,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(sK1)) | k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f646,f131])).
% 0.21/0.51  fof(f646,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3)))) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f645,f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK3)) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f193])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl5_3 <=> v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f645,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3)))) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(k2_funct_1(sK3))) ) | ~spl5_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f644,f198])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK3)) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f197])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    spl5_4 <=> v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f644,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3)))) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f643,f89])).
% 0.21/0.51  fof(f643,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3)))) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f635,f44])).
% 0.21/0.51  fof(f635,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k6_partfun1(k1_relat_1(X4)) != k6_partfun1(sK2) | ~r2_relset_1(X5,X6,k5_relat_1(sK3,X4),k6_partfun1(k2_relat_1(k2_funct_1(sK3)))) | ~m1_subset_1(k5_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_funct_1(sK3) = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(k2_funct_1(sK3))),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) )),
% 0.21/0.51    inference(superposition,[],[f189,f235])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f44])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f233,f45])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f232,f46])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f231,f52])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    ~v2_funct_1(sK3) | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f230,f54])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~v2_funct_1(sK3) | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f229])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    sK2 != sK2 | k1_xboole_0 = sK2 | ~v2_funct_1(sK3) | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.51    inference(superposition,[],[f74,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k5_relat_1(X0,X3) != k6_partfun1(k1_relat_1(X4)) | ~r2_relset_1(X1,X2,k5_relat_1(X3,X4),k6_partfun1(k2_relat_1(X0))) | ~m1_subset_1(k5_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | X0 = X4 | ~m1_subset_1(k6_partfun1(k2_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(extensionality_resolution,[],[f75,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f63,f56,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f210])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    $false | spl5_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f89])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl5_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f44])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl5_4),
% 0.21/0.52    inference(resolution,[],[f199,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ~v1_funct_1(k2_funct_1(sK3)) | spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f197])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    $false | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f205,f89])).
% 0.21/0.52  % (4285)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f204,f44])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl5_3),
% 0.21/0.52    inference(resolution,[],[f195,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ~v1_relat_1(k2_funct_1(sK3)) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f193])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (4262)------------------------------
% 0.21/0.52  % (4262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4262)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (4262)Memory used [KB]: 11641
% 0.21/0.52  % (4262)Time elapsed: 0.111 s
% 0.21/0.52  % (4262)------------------------------
% 0.21/0.52  % (4262)------------------------------
% 0.21/0.52  % (4255)Success in time 0.162 s
%------------------------------------------------------------------------------
