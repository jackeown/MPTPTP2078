%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0991+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   27 (  76 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 640 expanded)
%              Number of equality atoms :    7 (  56 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9334,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9333,f4366])).

fof(f4366,plain,(
    v1_funct_1(sK38) ),
    inference(cnf_transformation,[],[f3153])).

fof(f3153,plain,
    ( ~ v2_funct_1(sK38)
    & r2_relset_1(sK36,sK36,k1_partfun1(sK36,sK37,sK37,sK36,sK38,sK39),k6_partfun1(sK36))
    & m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36)))
    & v1_funct_2(sK39,sK37,sK36)
    & v1_funct_1(sK39)
    & k1_xboole_0 != sK37
    & m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    & v1_funct_2(sK38,sK36,sK37)
    & v1_funct_1(sK38) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37,sK38,sK39])],[f1557,f3152,f3151])).

fof(f3151,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK38)
      & ? [X3] :
          ( r2_relset_1(sK36,sK36,k1_partfun1(sK36,sK37,sK37,sK36,sK38,X3),k6_partfun1(sK36))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36)))
          & v1_funct_2(X3,sK37,sK36)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK37
      & m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
      & v1_funct_2(sK38,sK36,sK37)
      & v1_funct_1(sK38) ) ),
    introduced(choice_axiom,[])).

fof(f3152,plain,
    ( ? [X3] :
        ( r2_relset_1(sK36,sK36,k1_partfun1(sK36,sK37,sK37,sK36,sK38,X3),k6_partfun1(sK36))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36)))
        & v1_funct_2(X3,sK37,sK36)
        & v1_funct_1(X3) )
   => ( r2_relset_1(sK36,sK36,k1_partfun1(sK36,sK37,sK37,sK36,sK38,sK39),k6_partfun1(sK36))
      & m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36)))
      & v1_funct_2(sK39,sK37,sK36)
      & v1_funct_1(sK39) ) ),
    introduced(choice_axiom,[])).

fof(f1557,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1556])).

fof(f1556,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1512])).

fof(f1512,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f1511])).

fof(f1511,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

fof(f9333,plain,(
    ~ v1_funct_1(sK38) ),
    inference(subsumption_resolution,[],[f9332,f4367])).

fof(f4367,plain,(
    v1_funct_2(sK38,sK36,sK37) ),
    inference(cnf_transformation,[],[f3153])).

fof(f9332,plain,
    ( ~ v1_funct_2(sK38,sK36,sK37)
    | ~ v1_funct_1(sK38) ),
    inference(subsumption_resolution,[],[f9331,f4368])).

fof(f4368,plain,(
    m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37))) ),
    inference(cnf_transformation,[],[f3153])).

fof(f9331,plain,
    ( ~ m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    | ~ v1_funct_2(sK38,sK36,sK37)
    | ~ v1_funct_1(sK38) ),
    inference(subsumption_resolution,[],[f9330,f4370])).

fof(f4370,plain,(
    v1_funct_1(sK39) ),
    inference(cnf_transformation,[],[f3153])).

fof(f9330,plain,
    ( ~ v1_funct_1(sK39)
    | ~ m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    | ~ v1_funct_2(sK38,sK36,sK37)
    | ~ v1_funct_1(sK38) ),
    inference(subsumption_resolution,[],[f9329,f4371])).

fof(f4371,plain,(
    v1_funct_2(sK39,sK37,sK36) ),
    inference(cnf_transformation,[],[f3153])).

fof(f9329,plain,
    ( ~ v1_funct_2(sK39,sK37,sK36)
    | ~ v1_funct_1(sK39)
    | ~ m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    | ~ v1_funct_2(sK38,sK36,sK37)
    | ~ v1_funct_1(sK38) ),
    inference(subsumption_resolution,[],[f9328,f4372])).

fof(f4372,plain,(
    m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36))) ),
    inference(cnf_transformation,[],[f3153])).

fof(f9328,plain,
    ( ~ m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36)))
    | ~ v1_funct_2(sK39,sK37,sK36)
    | ~ v1_funct_1(sK39)
    | ~ m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    | ~ v1_funct_2(sK38,sK36,sK37)
    | ~ v1_funct_1(sK38) ),
    inference(subsumption_resolution,[],[f9325,f4374])).

fof(f4374,plain,(
    ~ v2_funct_1(sK38) ),
    inference(cnf_transformation,[],[f3153])).

fof(f9325,plain,
    ( v2_funct_1(sK38)
    | ~ m1_subset_1(sK39,k1_zfmisc_1(k2_zfmisc_1(sK37,sK36)))
    | ~ v1_funct_2(sK39,sK37,sK36)
    | ~ v1_funct_1(sK39)
    | ~ m1_subset_1(sK38,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    | ~ v1_funct_2(sK38,sK36,sK37)
    | ~ v1_funct_1(sK38) ),
    inference(resolution,[],[f4373,f6408])).

fof(f6408,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2724])).

fof(f2724,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2723])).

fof(f2723,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1503])).

fof(f1503,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f4373,plain,(
    r2_relset_1(sK36,sK36,k1_partfun1(sK36,sK37,sK37,sK36,sK38,sK39),k6_partfun1(sK36)) ),
    inference(cnf_transformation,[],[f3153])).
%------------------------------------------------------------------------------
