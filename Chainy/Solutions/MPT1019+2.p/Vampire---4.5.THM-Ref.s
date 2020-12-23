%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1019+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 115 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  211 (1037 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6107,f6098])).

fof(f6098,plain,(
    ~ v2_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6097,f3779])).

fof(f3779,plain,(
    v1_funct_1(sK215) ),
    inference(cnf_transformation,[],[f2908])).

fof(f2908,plain,
    ( ~ r2_relset_1(sK213,sK213,sK214,k6_partfun1(sK213))
    & r2_relset_1(sK213,sK213,k1_partfun1(sK213,sK213,sK213,sK213,sK214,sK215),sK215)
    & m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    & v3_funct_2(sK215,sK213,sK213)
    & v1_funct_2(sK215,sK213,sK213)
    & v1_funct_1(sK215)
    & m1_subset_1(sK214,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    & v3_funct_2(sK214,sK213,sK213)
    & v1_funct_2(sK214,sK213,sK213)
    & v1_funct_1(sK214) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK213,sK214,sK215])],[f1581,f2907,f2906])).

fof(f2906,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK213,sK213,sK214,k6_partfun1(sK213))
          & r2_relset_1(sK213,sK213,k1_partfun1(sK213,sK213,sK213,sK213,sK214,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
          & v3_funct_2(X2,sK213,sK213)
          & v1_funct_2(X2,sK213,sK213)
          & v1_funct_1(X2) )
      & m1_subset_1(sK214,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
      & v3_funct_2(sK214,sK213,sK213)
      & v1_funct_2(sK214,sK213,sK213)
      & v1_funct_1(sK214) ) ),
    introduced(choice_axiom,[])).

fof(f2907,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK213,sK213,sK214,k6_partfun1(sK213))
        & r2_relset_1(sK213,sK213,k1_partfun1(sK213,sK213,sK213,sK213,sK214,X2),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
        & v3_funct_2(X2,sK213,sK213)
        & v1_funct_2(X2,sK213,sK213)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK213,sK213,sK214,k6_partfun1(sK213))
      & r2_relset_1(sK213,sK213,k1_partfun1(sK213,sK213,sK213,sK213,sK214,sK215),sK215)
      & m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
      & v3_funct_2(sK215,sK213,sK213)
      & v1_funct_2(sK215,sK213,sK213)
      & v1_funct_1(sK215) ) ),
    introduced(choice_axiom,[])).

fof(f1581,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f1580])).

fof(f1580,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1561])).

fof(f1561,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
             => r2_relset_1(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1560])).

fof(f1560,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
           => r2_relset_1(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_2)).

fof(f6097,plain,
    ( ~ v2_funct_1(sK215)
    | ~ v1_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6096,f3780])).

fof(f3780,plain,(
    v1_funct_2(sK215,sK213,sK213) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6096,plain,
    ( ~ v2_funct_1(sK215)
    | ~ v1_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6095,f3782])).

fof(f3782,plain,(
    m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213))) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6095,plain,
    ( ~ v2_funct_1(sK215)
    | ~ m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6094,f3775])).

fof(f3775,plain,(
    v1_funct_1(sK214) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6094,plain,
    ( ~ v2_funct_1(sK215)
    | ~ v1_funct_1(sK214)
    | ~ m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6093,f3776])).

fof(f3776,plain,(
    v1_funct_2(sK214,sK213,sK213) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6093,plain,
    ( ~ v2_funct_1(sK215)
    | ~ v1_funct_2(sK214,sK213,sK213)
    | ~ v1_funct_1(sK214)
    | ~ m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6092,f3778])).

fof(f3778,plain,(
    m1_subset_1(sK214,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213))) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6092,plain,
    ( ~ v2_funct_1(sK215)
    | ~ m1_subset_1(sK214,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK214,sK213,sK213)
    | ~ v1_funct_1(sK214)
    | ~ m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215) ),
    inference(subsumption_resolution,[],[f6090,f3784])).

fof(f3784,plain,(
    ~ r2_relset_1(sK213,sK213,sK214,k6_partfun1(sK213)) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6090,plain,
    ( ~ v2_funct_1(sK215)
    | r2_relset_1(sK213,sK213,sK214,k6_partfun1(sK213))
    | ~ m1_subset_1(sK214,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK214,sK213,sK213)
    | ~ v1_funct_1(sK214)
    | ~ m1_subset_1(sK215,k1_zfmisc_1(k2_zfmisc_1(sK213,sK213)))
    | ~ v1_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215) ),
    inference(resolution,[],[f3783,f3791])).

fof(f3791,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
      | ~ v2_funct_1(X1)
      | r2_relset_1(X0,X0,X2,k6_partfun1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f1593])).

fof(f1593,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          | ~ v2_funct_1(X1)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v1_funct_2(X2,X0,X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f1592])).

fof(f1592,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          | ~ v2_funct_1(X1)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v1_funct_2(X2,X0,X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1555])).

fof(f1555,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f3783,plain,(
    r2_relset_1(sK213,sK213,k1_partfun1(sK213,sK213,sK213,sK213,sK214,sK215),sK215) ),
    inference(cnf_transformation,[],[f2908])).

fof(f6107,plain,(
    v2_funct_1(sK215) ),
    inference(resolution,[],[f6055,f3921])).

fof(f3921,plain,(
    ! [X0,X1] :
      ( ~ sP13(X0,X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f2969])).

fof(f2969,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP13(X0,X1) ) ),
    inference(rectify,[],[f2968])).

fof(f2968,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP13(X1,X2) ) ),
    inference(nnf_transformation,[],[f2602])).

fof(f2602,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP13(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f6055,plain,(
    sP13(sK213,sK215) ),
    inference(subsumption_resolution,[],[f6054,f3779])).

fof(f6054,plain,
    ( ~ v1_funct_1(sK215)
    | sP13(sK213,sK215) ),
    inference(subsumption_resolution,[],[f5981,f3781])).

fof(f3781,plain,(
    v3_funct_2(sK215,sK213,sK213) ),
    inference(cnf_transformation,[],[f2908])).

fof(f5981,plain,
    ( ~ v3_funct_2(sK215,sK213,sK213)
    | ~ v1_funct_1(sK215)
    | sP13(sK213,sK215) ),
    inference(resolution,[],[f3782,f3923])).

fof(f3923,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP13(X1,X2) ) ),
    inference(cnf_transformation,[],[f2603])).

fof(f2603,plain,(
    ! [X0,X1,X2] :
      ( sP13(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f1670,f2602])).

fof(f1670,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1669])).

fof(f1669,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1470])).

fof(f1470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
%------------------------------------------------------------------------------
