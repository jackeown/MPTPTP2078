%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 589 expanded)
%              Number of leaves         :   31 ( 246 expanded)
%              Depth                    :   18
%              Number of atoms          :  616 (4868 expanded)
%              Number of equality atoms :  106 (1132 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17245)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f1029,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f139,f173,f179,f292,f626,f729,f752,f789,f803,f810,f1028])).

fof(f1028,plain,
    ( ~ spl7_1
    | ~ spl7_51 ),
    inference(avatar_contradiction_clause,[],[f1027])).

fof(f1027,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f1017,f903])).

fof(f903,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f81,f515])).

fof(f515,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f269,f78])).

fof(f78,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f63,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f269,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f268,f72])).

fof(f72,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f268,plain,(
    ! [X0] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f267,f73])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f267,plain,(
    ! [X0] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f266,f74])).

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f266,plain,(
    ! [X0] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f265,f75])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

fof(f265,plain,(
    ! [X0] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f264,f76])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f264,plain,(
    ! [X0] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f263,f77])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f263,plain,(
    ! [X0] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f261,f80])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f64])).

fof(f261,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f79,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f79,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f64])).

fof(f81,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f1017,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl7_1
    | ~ spl7_51 ),
    inference(resolution,[],[f1015,f130])).

fof(f130,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_1
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1015,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl7_51 ),
    inference(resolution,[],[f902,f204])).

fof(f204,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(resolution,[],[f77,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f902,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK4,X1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f901,f200])).

fof(f200,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f77,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f901,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0))
        | ~ v5_relat_1(sK4,X1)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f899,f76])).

fof(f899,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0))
        | ~ v1_funct_1(sK4)
        | ~ v5_relat_1(sK4,X1)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_51 ),
    inference(resolution,[],[f747,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f747,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl7_51
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f810,plain,
    ( ~ spl7_37
    | spl7_38 ),
    inference(avatar_split_clause,[],[f808,f464,f460])).

fof(f460,plain,
    ( spl7_37
  <=> r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f464,plain,
    ( spl7_38
  <=> k2_relat_1(sK3) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f808,plain,
    ( k2_relat_1(sK3) = k1_relat_1(sK4)
    | ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) ),
    inference(resolution,[],[f451,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f451,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f428,f201])).

fof(f201,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f77,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f428,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(backward_demodulation,[],[f79,f144])).

fof(f144,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f75,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f803,plain,
    ( ~ spl7_38
    | spl7_42
    | ~ spl7_52 ),
    inference(avatar_contradiction_clause,[],[f802])).

fof(f802,plain,
    ( $false
    | ~ spl7_38
    | spl7_42
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f801,f567])).

fof(f567,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl7_42
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f801,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl7_38
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f466,f751])).

fof(f751,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl7_52
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f466,plain,
    ( k2_relat_1(sK3) = k1_relat_1(sK4)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f464])).

fof(f789,plain,
    ( spl7_37
    | ~ spl7_52 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | spl7_37
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f780,f83])).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f780,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | spl7_37
    | ~ spl7_52 ),
    inference(backward_demodulation,[],[f462,f751])).

fof(f462,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | spl7_37 ),
    inference(avatar_component_clause,[],[f460])).

fof(f752,plain,
    ( spl7_51
    | spl7_52
    | ~ spl7_5
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f744,f718,f171,f749,f746])).

fof(f171,plain,
    ( spl7_5
  <=> ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | v1_funct_2(sK3,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f718,plain,
    ( spl7_49
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f744,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK4)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl7_5
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f743,f73])).

fof(f743,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK4)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
        | ~ v1_funct_1(sK3) )
    | ~ spl7_5
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f736,f483])).

fof(f483,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl7_5 ),
    inference(resolution,[],[f480,f451])).

fof(f480,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),X1)
        | v1_funct_2(sK3,sK1,X1) )
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f172,f144])).

fof(f172,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | v1_funct_2(sK3,sK1,X1) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f736,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK4)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
        | ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
        | ~ v1_funct_1(sK3) )
    | ~ spl7_49 ),
    inference(resolution,[],[f719,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f719,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f718])).

fof(f729,plain,
    ( ~ spl7_6
    | spl7_49 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | ~ spl7_6
    | spl7_49 ),
    inference(subsumption_resolution,[],[f726,f451])).

fof(f726,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl7_6
    | spl7_49 ),
    inference(resolution,[],[f720,f486])).

fof(f486,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
        | ~ r1_tarski(k2_relat_1(sK3),X2) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f178,f144])).

fof(f178,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_6
  <=> ! [X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f720,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | spl7_49 ),
    inference(avatar_component_clause,[],[f718])).

fof(f626,plain,
    ( spl7_2
    | ~ spl7_42 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | spl7_2
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f624,f157])).

fof(f157,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f156,f133])).

fof(f133,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f156,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f155,f72])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f154,f73])).

fof(f154,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f141,f74])).

fof(f141,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f75,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f624,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f623,f142])).

fof(f142,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f109])).

fof(f623,plain,
    ( ~ v1_relat_1(sK3)
    | v1_xboole_0(sK3)
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f611,f82])).

fof(f82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f611,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | v1_xboole_0(sK3)
    | ~ spl7_42 ),
    inference(superposition,[],[f87,f568])).

fof(f568,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f566])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f292,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f290,f82])).

fof(f290,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f72,f166])).

fof(f166,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f179,plain,
    ( spl7_6
    | spl7_4 ),
    inference(avatar_split_clause,[],[f175,f164,f177])).

fof(f175,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f174,f73])).

fof(f174,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f149,f74])).

fof(f149,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f75,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f173,plain,
    ( spl7_5
    | spl7_4 ),
    inference(avatar_split_clause,[],[f169,f164,f171])).

fof(f169,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f168,f73])).

fof(f168,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f148,f74])).

fof(f148,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f75,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f139,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f136,f80])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(resolution,[],[f134,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f134,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f78,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (17238)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.48  % (17263)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (17255)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  % (17241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (17246)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (17259)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (17261)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (17253)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (17244)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (17238)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (17245)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  fof(f1029,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f135,f139,f173,f179,f292,f626,f729,f752,f789,f803,f810,f1028])).
% 0.22/0.52  fof(f1028,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_51),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1027])).
% 0.22/0.52  fof(f1027,plain,(
% 0.22/0.52    $false | (~spl7_1 | ~spl7_51)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1017,f903])).
% 0.22/0.52  fof(f903,plain,(
% 0.22/0.52    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.52    inference(backward_demodulation,[],[f81,f515])).
% 0.22/0.52  fof(f515,plain,(
% 0.22/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.52    inference(resolution,[],[f269,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    m1_subset_1(sK5,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f63,f62,f61,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f27])).
% 0.22/0.52  fof(f27,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f268,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~v1_xboole_0(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f267,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f267,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f266,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f265,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f264,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    v1_funct_1(sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f263,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f261,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f79,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.52    inference(flattening,[],[f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.52    inference(cnf_transformation,[],[f64])).
% 0.22/0.52  fof(f1017,plain,(
% 0.22/0.52    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl7_1 | ~spl7_51)),
% 0.22/0.52    inference(resolution,[],[f1015,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    r2_hidden(sK5,sK1) | ~spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl7_1 <=> r2_hidden(sK5,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f1015,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0))) ) | ~spl7_51),
% 0.22/0.52    inference(resolution,[],[f902,f204])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    v5_relat_1(sK4,sK0)),
% 0.22/0.52    inference(resolution,[],[f77,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f902,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v5_relat_1(sK4,X1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)) | ~r2_hidden(X0,sK1)) ) | ~spl7_51),
% 0.22/0.52    inference(subsumption_resolution,[],[f901,f200])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    v1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f77,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f901,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) ) | ~spl7_51),
% 0.22/0.52    inference(subsumption_resolution,[],[f899,f76])).
% 0.22/0.52  fof(f899,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) ) | ~spl7_51),
% 0.22/0.52    inference(resolution,[],[f747,f101])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.52  fof(f747,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | ~r2_hidden(X0,sK1)) ) | ~spl7_51),
% 0.22/0.52    inference(avatar_component_clause,[],[f746])).
% 0.22/0.52  fof(f746,plain,(
% 0.22/0.52    spl7_51 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 0.22/0.52  fof(f810,plain,(
% 0.22/0.52    ~spl7_37 | spl7_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f808,f464,f460])).
% 0.22/0.52  fof(f460,plain,(
% 0.22/0.52    spl7_37 <=> r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.52  fof(f464,plain,(
% 0.22/0.52    spl7_38 <=> k2_relat_1(sK3) = k1_relat_1(sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.52  fof(f808,plain,(
% 0.22/0.52    k2_relat_1(sK3) = k1_relat_1(sK4) | ~r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))),
% 0.22/0.52    inference(resolution,[],[f451,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f451,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.22/0.52    inference(backward_demodulation,[],[f428,f201])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f77,f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f428,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.52    inference(backward_demodulation,[],[f79,f144])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f75,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f803,plain,(
% 0.22/0.52    ~spl7_38 | spl7_42 | ~spl7_52),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f802])).
% 0.22/0.52  fof(f802,plain,(
% 0.22/0.52    $false | (~spl7_38 | spl7_42 | ~spl7_52)),
% 0.22/0.52    inference(subsumption_resolution,[],[f801,f567])).
% 0.22/0.52  fof(f567,plain,(
% 0.22/0.52    k1_xboole_0 != k2_relat_1(sK3) | spl7_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f566])).
% 0.22/0.52  fof(f566,plain,(
% 0.22/0.52    spl7_42 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.22/0.52  fof(f801,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(sK3) | (~spl7_38 | ~spl7_52)),
% 0.22/0.52    inference(forward_demodulation,[],[f466,f751])).
% 0.22/0.52  fof(f751,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK4) | ~spl7_52),
% 0.22/0.52    inference(avatar_component_clause,[],[f749])).
% 0.22/0.52  fof(f749,plain,(
% 0.22/0.52    spl7_52 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.22/0.52  fof(f466,plain,(
% 0.22/0.52    k2_relat_1(sK3) = k1_relat_1(sK4) | ~spl7_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f464])).
% 0.22/0.52  fof(f789,plain,(
% 0.22/0.52    spl7_37 | ~spl7_52),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f788])).
% 0.22/0.52  fof(f788,plain,(
% 0.22/0.52    $false | (spl7_37 | ~spl7_52)),
% 0.22/0.52    inference(subsumption_resolution,[],[f780,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f780,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | (spl7_37 | ~spl7_52)),
% 0.22/0.52    inference(backward_demodulation,[],[f462,f751])).
% 0.22/0.52  fof(f462,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) | spl7_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f460])).
% 0.22/0.52  fof(f752,plain,(
% 0.22/0.52    spl7_51 | spl7_52 | ~spl7_5 | ~spl7_49),
% 0.22/0.52    inference(avatar_split_clause,[],[f744,f718,f171,f749,f746])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl7_5 <=> ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.52  fof(f718,plain,(
% 0.22/0.52    spl7_49 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 0.22/0.52  fof(f744,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK4) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | (~spl7_5 | ~spl7_49)),
% 0.22/0.52    inference(subsumption_resolution,[],[f743,f73])).
% 0.22/0.52  fof(f743,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK4) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | ~v1_funct_1(sK3)) ) | (~spl7_5 | ~spl7_49)),
% 0.22/0.52    inference(subsumption_resolution,[],[f736,f483])).
% 0.22/0.52  fof(f483,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~spl7_5),
% 0.22/0.52    inference(resolution,[],[f480,f451])).
% 0.22/0.52  fof(f480,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_tarski(k2_relat_1(sK3),X1) | v1_funct_2(sK3,sK1,X1)) ) | ~spl7_5),
% 0.22/0.52    inference(forward_demodulation,[],[f172,f144])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1)) ) | ~spl7_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f171])).
% 0.22/0.52  fof(f736,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK4) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~v1_funct_1(sK3)) ) | ~spl7_49),
% 0.22/0.52    inference(resolution,[],[f719,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.52  fof(f719,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | ~spl7_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f718])).
% 0.22/0.52  fof(f729,plain,(
% 0.22/0.52    ~spl7_6 | spl7_49),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f728])).
% 0.22/0.52  fof(f728,plain,(
% 0.22/0.52    $false | (~spl7_6 | spl7_49)),
% 0.22/0.52    inference(subsumption_resolution,[],[f726,f451])).
% 0.22/0.52  fof(f726,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl7_6 | spl7_49)),
% 0.22/0.52    inference(resolution,[],[f720,f486])).
% 0.22/0.52  fof(f486,plain,(
% 0.22/0.52    ( ! [X2] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~r1_tarski(k2_relat_1(sK3),X2)) ) | ~spl7_6),
% 0.22/0.52    inference(forward_demodulation,[],[f178,f144])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | ~spl7_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f177])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    spl7_6 <=> ! [X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.52  fof(f720,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | spl7_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f718])).
% 0.22/0.52  fof(f626,plain,(
% 0.22/0.52    spl7_2 | ~spl7_42),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f625])).
% 0.22/0.52  fof(f625,plain,(
% 0.22/0.52    $false | (spl7_2 | ~spl7_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f624,f157])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ~v1_xboole_0(sK3) | spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f156,f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~v1_xboole_0(sK1) | spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl7_2 <=> v1_xboole_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ~v1_xboole_0(sK3) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f72])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ~v1_xboole_0(sK3) | v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f154,f73])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | ~v1_xboole_0(sK3) | v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f74])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~v1_xboole_0(sK3) | v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f75,f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,axiom,(
% 0.22/0.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 0.22/0.52  fof(f624,plain,(
% 0.22/0.52    v1_xboole_0(sK3) | ~spl7_42),
% 0.22/0.52    inference(subsumption_resolution,[],[f623,f142])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f75,f109])).
% 0.22/0.52  fof(f623,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | v1_xboole_0(sK3) | ~spl7_42),
% 0.22/0.52    inference(subsumption_resolution,[],[f611,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f611,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK3) | v1_xboole_0(sK3) | ~spl7_42),
% 0.22/0.52    inference(superposition,[],[f87,f568])).
% 0.22/0.52  fof(f568,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(sK3) | ~spl7_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f566])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.52  fof(f292,plain,(
% 0.22/0.52    ~spl7_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f291])).
% 0.22/0.52  fof(f291,plain,(
% 0.22/0.52    $false | ~spl7_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f290,f82])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl7_4),
% 0.22/0.52    inference(backward_demodulation,[],[f72,f166])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | ~spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f164])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    spl7_4 <=> k1_xboole_0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    spl7_6 | spl7_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f175,f164,f177])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f174,f73])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_1(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f149,f74])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f75,f119])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    spl7_5 | spl7_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f169,f164,f171])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f168,f73])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1) | ~v1_funct_1(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f148,f74])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f75,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f59])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~spl7_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    $false | ~spl7_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f136,f80])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl7_2),
% 0.22/0.52    inference(resolution,[],[f134,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | ~spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f132])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl7_1 | spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f126,f132,f128])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | r2_hidden(sK5,sK1)),
% 0.22/0.52    inference(resolution,[],[f78,f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (17238)------------------------------
% 0.22/0.52  % (17238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17238)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (17238)Memory used [KB]: 11129
% 0.22/0.52  % (17238)Time elapsed: 0.126 s
% 0.22/0.52  % (17238)------------------------------
% 0.22/0.52  % (17238)------------------------------
% 1.24/0.52  % (17250)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.24/0.52  % (17264)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.24/0.52  % (17252)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.52  % (17243)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.24/0.53  % (17257)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.24/0.53  % (17240)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.24/0.53  % (17260)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.24/0.53  % (17242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.24/0.53  % (17236)Success in time 0.175 s
%------------------------------------------------------------------------------
