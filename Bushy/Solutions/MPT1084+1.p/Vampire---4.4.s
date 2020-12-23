%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t201_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 7.17s
% Output     : Refutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 281 expanded)
%              Number of leaves         :   12 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  297 (1603 expanded)
%              Number of equality atoms :   40 ( 237 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3762,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f76,f128,f107,f77,f108,f195,f703,f270])).

fof(f270,plain,(
    ! [X19,X20,X18] :
      ( ~ r2_hidden(sK3(X18,sK1,k6_relat_1(X19)),X19)
      | ~ m1_subset_1(k6_relat_1(X19),k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
      | ~ v1_funct_2(k6_relat_1(X19),X18,X20)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
      | ~ v1_funct_2(sK1,X18,X20)
      | r2_funct_2(X18,X20,sK1,k6_relat_1(X19))
      | ~ m1_subset_1(sK3(X18,sK1,k6_relat_1(X19)),sK0) ) ),
    inference(subsumption_resolution,[],[f265,f75])).

fof(f75,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
          & ! [X2] :
              ( k3_funct_2(sK0,sK0,X1,X2) = X2
              | ~ m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
     => ( ~ r2_funct_2(X0,X0,sK1,k6_partfun1(X0))
        & ! [X2] :
            ( k3_funct_2(X0,X0,sK1,X2) = X2
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK1,X0,X0)
        & v1_funct_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t201_funct_2)).

fof(f265,plain,(
    ! [X19,X20,X18] :
      ( r2_funct_2(X18,X20,sK1,k6_relat_1(X19))
      | ~ m1_subset_1(k6_relat_1(X19),k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
      | ~ v1_funct_2(k6_relat_1(X19),X18,X20)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
      | ~ v1_funct_2(sK1,X18,X20)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(sK3(X18,sK1,k6_relat_1(X19)),X19)
      | ~ m1_subset_1(sK3(X18,sK1,k6_relat_1(X19)),sK0) ) ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,(
    ! [X19,X20,X18] :
      ( sK3(X18,sK1,k6_relat_1(X19)) != sK3(X18,sK1,k6_relat_1(X19))
      | r2_funct_2(X18,X20,sK1,k6_relat_1(X19))
      | ~ m1_subset_1(k6_relat_1(X19),k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
      | ~ v1_funct_2(k6_relat_1(X19),X18,X20)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
      | ~ v1_funct_2(sK1,X18,X20)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(sK3(X18,sK1,k6_relat_1(X19)),X19)
      | ~ m1_subset_1(sK3(X18,sK1,k6_relat_1(X19)),sK0) ) ),
    inference(superposition,[],[f183,f149])).

fof(f149,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f148,f74])).

fof(f74,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f148,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f147,f75])).

fof(f147,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f76])).

fof(f146,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f77])).

fof(f145,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(superposition,[],[f101,f78])).

fof(f78,plain,(
    ! [X2] :
      ( k3_funct_2(sK0,sK0,sK1,X2) = X2
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',redefinition_k3_funct_2)).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK3(X1,X2,k6_relat_1(X0))) != sK3(X1,X2,k6_relat_1(X0))
      | r2_funct_2(X1,X3,X2,k6_relat_1(X0))
      | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(k6_relat_1(X0),X1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(X2,X1,X3)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(sK3(X1,X2,k6_relat_1(X0)),X0) ) ),
    inference(subsumption_resolution,[],[f173,f82])).

fof(f82,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',fc3_funct_1)).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK3(X1,X2,k6_relat_1(X0))) != sK3(X1,X2,k6_relat_1(X0))
      | r2_funct_2(X1,X3,X2,k6_relat_1(X0))
      | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(k6_relat_1(X0),X1,X3)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_2(X2,X1,X3)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(sK3(X1,X2,k6_relat_1(X0)),X0) ) ),
    inference(superposition,[],[f97,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t35_funct_1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
                & m1_subset_1(sK3(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f68,f69])).

fof(f69,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
        & m1_subset_1(sK3(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',d9_funct_2)).

fof(f703,plain,(
    r2_hidden(sK3(sK0,sK1,k6_relat_1(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f195,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t2_subset)).

fof(f195,plain,(
    m1_subset_1(sK3(sK0,sK1,k6_relat_1(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f75,f82,f76,f77,f107,f108,f128,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X2,X3),X0)
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f84,f81])).

fof(f81,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',dt_k6_partfun1)).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f107,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f79,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f128,plain,(
    ! [X0] : v1_funct_2(k6_relat_1(X0),X0,X0) ),
    inference(unit_resulting_resolution,[],[f82,f109,f108,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',cc1_funct_2)).

fof(f109,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f83,f81])).

fof(f83,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
