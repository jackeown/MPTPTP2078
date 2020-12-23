%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1033+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 4.97s
% Output     : Refutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 414 expanded)
%              Number of leaves         :   14 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  416 (3697 expanded)
%              Number of equality atoms :   56 ( 728 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8265,plain,(
    $false ),
    inference(global_subsumption,[],[f5196,f5142,f8238,f8248,f8264])).

fof(f8264,plain,(
    k1_xboole_0 != sK157 ),
    inference(subsumption_resolution,[],[f8263,f4193])).

fof(f4193,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f8263,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK157 ),
    inference(superposition,[],[f8248,f3323])).

fof(f3323,plain,
    ( k1_xboole_0 = sK156
    | k1_xboole_0 != sK157 ),
    inference(cnf_transformation,[],[f2652])).

fof(f2652,plain,
    ( ~ r2_relset_1(sK156,sK157,sK158,sK159)
    & ( k1_xboole_0 = sK156
      | k1_xboole_0 != sK157 )
    & r1_partfun1(sK158,sK159)
    & m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
    & v1_funct_2(sK159,sK156,sK157)
    & v1_funct_1(sK159)
    & m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
    & v1_funct_2(sK158,sK156,sK157)
    & v1_funct_1(sK158) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK156,sK157,sK158,sK159])],[f1608,f2651,f2650])).

fof(f2650,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK156,sK157,sK158,X3)
          & ( k1_xboole_0 = sK156
            | k1_xboole_0 != sK157 )
          & r1_partfun1(sK158,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
          & v1_funct_2(X3,sK156,sK157)
          & v1_funct_1(X3) )
      & m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      & v1_funct_2(sK158,sK156,sK157)
      & v1_funct_1(sK158) ) ),
    introduced(choice_axiom,[])).

fof(f2651,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK156,sK157,sK158,X3)
        & ( k1_xboole_0 = sK156
          | k1_xboole_0 != sK157 )
        & r1_partfun1(sK158,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
        & v1_funct_2(X3,sK156,sK157)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK156,sK157,sK158,sK159)
      & ( k1_xboole_0 = sK156
        | k1_xboole_0 != sK157 )
      & r1_partfun1(sK158,sK159)
      & m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      & v1_funct_2(sK159,sK156,sK157)
      & v1_funct_1(sK159) ) ),
    introduced(choice_axiom,[])).

fof(f1608,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1607])).

fof(f1607,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1533])).

fof(f1533,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1532])).

fof(f1532,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f8248,plain,(
    ~ v1_xboole_0(sK156) ),
    inference(resolution,[],[f7868,f4157])).

fof(f4157,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2060,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f7868,plain,(
    r2_hidden(sK160(sK156,sK159,sK158),sK156) ),
    inference(subsumption_resolution,[],[f7867,f3319])).

fof(f3319,plain,(
    v1_funct_1(sK159) ),
    inference(cnf_transformation,[],[f2652])).

fof(f7867,plain,
    ( r2_hidden(sK160(sK156,sK159,sK158),sK156)
    | ~ v1_funct_1(sK159) ),
    inference(subsumption_resolution,[],[f7866,f3320])).

fof(f3320,plain,(
    v1_funct_2(sK159,sK156,sK157) ),
    inference(cnf_transformation,[],[f2652])).

fof(f7866,plain,
    ( r2_hidden(sK160(sK156,sK159,sK158),sK156)
    | ~ v1_funct_2(sK159,sK156,sK157)
    | ~ v1_funct_1(sK159) ),
    inference(subsumption_resolution,[],[f7831,f7483])).

fof(f7483,plain,(
    ~ r2_relset_1(sK156,sK157,sK159,sK158) ),
    inference(subsumption_resolution,[],[f7460,f3324])).

fof(f3324,plain,(
    ~ r2_relset_1(sK156,sK157,sK158,sK159) ),
    inference(cnf_transformation,[],[f2652])).

fof(f7460,plain,
    ( r2_relset_1(sK156,sK157,sK158,sK159)
    | ~ r2_relset_1(sK156,sK157,sK159,sK158) ),
    inference(resolution,[],[f5043,f3321])).

fof(f3321,plain,(
    m1_subset_1(sK159,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157))) ),
    inference(cnf_transformation,[],[f2652])).

fof(f5043,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      | r2_relset_1(sK156,sK157,sK158,X1)
      | ~ r2_relset_1(sK156,sK157,X1,sK158) ) ),
    inference(resolution,[],[f3318,f3327])).

fof(f3327,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1612])).

fof(f1612,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1611])).

fof(f1611,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1239])).

fof(f1239,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r2_relset_1)).

fof(f3318,plain,(
    m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157))) ),
    inference(cnf_transformation,[],[f2652])).

fof(f7831,plain,
    ( r2_relset_1(sK156,sK157,sK159,sK158)
    | r2_hidden(sK160(sK156,sK159,sK158),sK156)
    | ~ v1_funct_2(sK159,sK156,sK157)
    | ~ v1_funct_1(sK159) ),
    inference(resolution,[],[f5086,f3321])).

fof(f5086,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      | r2_relset_1(sK156,sK157,X2,sK158)
      | r2_hidden(sK160(sK156,X2,sK158),sK156)
      | ~ v1_funct_2(X2,sK156,sK157)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f5085,f3316])).

fof(f3316,plain,(
    v1_funct_1(sK158) ),
    inference(cnf_transformation,[],[f2652])).

fof(f5085,plain,(
    ! [X2] :
      ( r2_hidden(sK160(sK156,X2,sK158),sK156)
      | r2_relset_1(sK156,sK157,X2,sK158)
      | ~ v1_funct_1(sK158)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      | ~ v1_funct_2(X2,sK156,sK157)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f5044,f3317])).

fof(f3317,plain,(
    v1_funct_2(sK158,sK156,sK157) ),
    inference(cnf_transformation,[],[f2652])).

fof(f5044,plain,(
    ! [X2] :
      ( r2_hidden(sK160(sK156,X2,sK158),sK156)
      | r2_relset_1(sK156,sK157,X2,sK158)
      | ~ v1_funct_2(sK158,sK156,sK157)
      | ~ v1_funct_1(sK158)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      | ~ v1_funct_2(X2,sK156,sK157)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f3318,f3330])).

fof(f3330,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK160(X0,X2,X3),X0)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2655])).

fof(f2655,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK160(X0,X2,X3)) != k1_funct_1(X3,sK160(X0,X2,X3))
            & r2_hidden(sK160(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK160])],[f1618,f2654])).

fof(f2654,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK160(X0,X2,X3)) != k1_funct_1(X3,sK160(X0,X2,X3))
        & r2_hidden(sK160(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1618,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1617])).

fof(f1617,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1537])).

fof(f1537,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f8238,plain,(
    v1_xboole_0(sK157) ),
    inference(subsumption_resolution,[],[f8163,f5070])).

fof(f5070,plain,(
    r2_relset_1(sK156,sK157,sK158,sK158) ),
    inference(resolution,[],[f3318,f5035])).

fof(f5035,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f4940])).

fof(f4940,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f3326])).

fof(f3326,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2653])).

fof(f2653,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1610])).

fof(f1610,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1609])).

fof(f1609,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f8163,plain,
    ( ~ r2_relset_1(sK156,sK157,sK158,sK158)
    | v1_xboole_0(sK157) ),
    inference(superposition,[],[f3324,f8149])).

fof(f8149,plain,
    ( sK158 = sK159
    | v1_xboole_0(sK157) ),
    inference(resolution,[],[f7803,f5111])).

fof(f5111,plain,
    ( v1_partfun1(sK158,sK156)
    | v1_xboole_0(sK157) ),
    inference(subsumption_resolution,[],[f5110,f3316])).

fof(f5110,plain,
    ( ~ v1_funct_1(sK158)
    | v1_partfun1(sK158,sK156)
    | v1_xboole_0(sK157) ),
    inference(subsumption_resolution,[],[f5065,f3317])).

fof(f5065,plain,
    ( ~ v1_funct_2(sK158,sK156,sK157)
    | ~ v1_funct_1(sK158)
    | v1_partfun1(sK158,sK156)
    | v1_xboole_0(sK157) ),
    inference(resolution,[],[f3318,f3974])).

fof(f3974,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1941])).

fof(f1941,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f1940])).

fof(f1940,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1475])).

fof(f1475,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f7803,plain,
    ( ~ v1_partfun1(sK158,sK156)
    | sK158 = sK159 ),
    inference(global_subsumption,[],[f5143,f5190,f5063,f7802])).

fof(f7802,plain,
    ( ~ v1_partfun1(sK159,sK156)
    | ~ v1_partfun1(sK158,sK156)
    | sK158 = sK159 ),
    inference(subsumption_resolution,[],[f7801,f3316])).

fof(f7801,plain,
    ( ~ v1_partfun1(sK159,sK156)
    | ~ v1_partfun1(sK158,sK156)
    | sK158 = sK159
    | ~ v1_funct_1(sK158) ),
    inference(subsumption_resolution,[],[f7767,f3322])).

fof(f3322,plain,(
    r1_partfun1(sK158,sK159) ),
    inference(cnf_transformation,[],[f2652])).

fof(f7767,plain,
    ( ~ v1_partfun1(sK159,sK156)
    | ~ v1_partfun1(sK158,sK156)
    | sK158 = sK159
    | ~ r1_partfun1(sK158,sK159)
    | ~ v1_funct_1(sK158) ),
    inference(resolution,[],[f5171,f3318])).

fof(f5171,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      | ~ v1_partfun1(sK159,sK156)
      | ~ v1_partfun1(X4,sK156)
      | sK159 = X4
      | ~ r1_partfun1(X4,sK159)
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f5127,f3319])).

fof(f5127,plain,(
    ! [X4] :
      ( ~ r1_partfun1(X4,sK159)
      | ~ v1_partfun1(sK159,sK156)
      | ~ v1_partfun1(X4,sK156)
      | sK159 = X4
      | ~ v1_funct_1(sK159)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK156,sK157)))
      | ~ v1_funct_1(X4) ) ),
    inference(resolution,[],[f3321,f3415])).

fof(f3415,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1649])).

fof(f1649,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1648])).

fof(f1648,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1534])).

fof(f1534,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f5063,plain,
    ( ~ v1_partfun1(sK158,sK156)
    | ~ v1_xboole_0(sK157)
    | v1_xboole_0(sK156) ),
    inference(resolution,[],[f3318,f3967])).

fof(f3967,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1936])).

fof(f1936,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1935])).

fof(f1935,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f5190,plain,
    ( v1_partfun1(sK159,sK156)
    | v1_xboole_0(sK157) ),
    inference(subsumption_resolution,[],[f5189,f3319])).

fof(f5189,plain,
    ( ~ v1_funct_1(sK159)
    | v1_partfun1(sK159,sK156)
    | v1_xboole_0(sK157) ),
    inference(subsumption_resolution,[],[f5144,f3320])).

fof(f5144,plain,
    ( ~ v1_funct_2(sK159,sK156,sK157)
    | ~ v1_funct_1(sK159)
    | v1_partfun1(sK159,sK156)
    | v1_xboole_0(sK157) ),
    inference(resolution,[],[f3321,f3974])).

fof(f5143,plain,
    ( v1_partfun1(sK159,sK156)
    | ~ v1_xboole_0(sK156) ),
    inference(resolution,[],[f3321,f3972])).

fof(f3972,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1939])).

fof(f1939,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1469])).

fof(f1469,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f5142,plain,
    ( ~ v1_partfun1(sK159,sK156)
    | ~ v1_xboole_0(sK157)
    | v1_xboole_0(sK156) ),
    inference(resolution,[],[f3321,f3967])).

fof(f5196,plain,
    ( v1_partfun1(sK159,sK156)
    | k1_xboole_0 = sK157 ),
    inference(subsumption_resolution,[],[f5195,f3319])).

fof(f5195,plain,
    ( k1_xboole_0 = sK157
    | v1_partfun1(sK159,sK156)
    | ~ v1_funct_1(sK159) ),
    inference(subsumption_resolution,[],[f5151,f3320])).

fof(f5151,plain,
    ( k1_xboole_0 = sK157
    | v1_partfun1(sK159,sK156)
    | ~ v1_funct_2(sK159,sK156,sK157)
    | ~ v1_funct_1(sK159) ),
    inference(resolution,[],[f3321,f5041])).

fof(f5041,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f3959])).

fof(f3959,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1930])).

fof(f1930,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1929])).

fof(f1929,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1528])).

fof(f1528,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
%------------------------------------------------------------------------------
