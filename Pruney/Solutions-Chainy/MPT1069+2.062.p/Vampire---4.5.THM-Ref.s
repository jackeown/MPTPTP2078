%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:52 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 413 expanded)
%              Number of leaves         :   23 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  482 (3468 expanded)
%              Number of equality atoms :  123 ( 848 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(subsumption_resolution,[],[f315,f96])).

fof(f96,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f78,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f315,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f56,f314])).

fof(f314,plain,(
    k1_xboole_0 = sK3 ),
    inference(global_subsumption,[],[f267,f310])).

fof(f310,plain,(
    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(backward_demodulation,[],[f65,f309])).

fof(f309,plain,(
    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f308,f138])).

fof(f138,plain,(
    r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f123,f133])).

fof(f133,plain,(
    k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f43,f42,f41,f40])).

fof(f40,plain,
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
                  ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK2
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK2
                & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                & m1_subset_1(X5,sK2) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X3,sK2,sK3)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5))
              & k1_xboole_0 != sK2
              & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4))
              & m1_subset_1(X5,sK2) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5))
            & k1_xboole_0 != sK2
            & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4))
            & m1_subset_1(X5,sK2) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5))
          & k1_xboole_0 != sK2
          & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
          & m1_subset_1(X5,sK2) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5))
        & k1_xboole_0 != sK2
        & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
        & m1_subset_1(X5,sK2) )
   => ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))
      & k1_xboole_0 != sK2
      & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
      & m1_subset_1(sK6,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f123,plain,(
    r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(backward_demodulation,[],[f63,f121])).

fof(f121,plain,(
    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f80,f59])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f63,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f308,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(forward_demodulation,[],[f307,f133])).

fof(f307,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))
    | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f306,f60])).

fof(f60,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f306,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(resolution,[],[f252,f61])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1))
      | ~ v1_funct_1(X1)
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),sK6) = k1_funct_1(X1,k1_funct_1(sK4,sK6)) ) ),
    inference(resolution,[],[f212,f62])).

fof(f62,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,sK2)
      | ~ r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X1)
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) ) ),
    inference(forward_demodulation,[],[f211,f121])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
      | ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X1)
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) ) ),
    inference(subsumption_resolution,[],[f210,f56])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
      | ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X1)
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
      | v1_xboole_0(sK3) ) ),
    inference(subsumption_resolution,[],[f209,f57])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
      | ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X1)
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(sK3) ) ),
    inference(subsumption_resolution,[],[f208,f59])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
      | ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(sK3) ) ),
    inference(subsumption_resolution,[],[f207,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
      | ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(sK3) ) ),
    inference(resolution,[],[f79,f58])).

fof(f58,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f65,plain,(
    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f44])).

fof(f267,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f266,f64])).

fof(f266,plain,
    ( k1_xboole_0 = sK3
    | k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f262,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f262,plain,
    ( v1_xboole_0(sK2)
    | k1_xboole_0 = sK3
    | k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(resolution,[],[f190,f100])).

fof(f100,plain,
    ( r2_hidden(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f72,f62])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f190,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK5,k1_funct_1(sK4,X0)) = k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0))
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f173,f150])).

fof(f150,plain,
    ( sK2 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f149,f132])).

fof(f132,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK2,sK3,sK4) ),
    inference(resolution,[],[f81,f59])).

fof(f149,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f148,f117])).

fof(f117,plain,(
    sP0(sK2,sK4,sK3) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (29018)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f148,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ sP0(sK2,sK4,sK3) ),
    inference(resolution,[],[f83,f58])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK5,k1_funct_1(sK4,X0)) = k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) ) ),
    inference(resolution,[],[f172,f147])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5))
      | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f146,f108])).

fof(f108,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f99,f59])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f68,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) ) ),
    inference(subsumption_resolution,[],[f145,f57])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) ) ),
    inference(resolution,[],[f73,f136])).

fof(f136,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_relat_1(sK4))
      | r2_hidden(X4,k1_relat_1(sK5)) ) ),
    inference(backward_demodulation,[],[f125,f133])).

fof(f125,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_relat_1(sK4))
      | r2_hidden(X4,k1_relset_1(sK3,sK1,sK5)) ) ),
    inference(backward_demodulation,[],[f114,f121])).

fof(f114,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_relset_1(sK2,sK3,sK4))
      | r2_hidden(X4,k1_relset_1(sK3,sK1,sK5)) ) ),
    inference(resolution,[],[f75,f63])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

% (29020)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f172,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK5))
      | k1_funct_1(sK5,X0) = k7_partfun1(sK1,sK5,X0) ) ),
    inference(resolution,[],[f158,f116])).

fof(f116,plain,(
    v5_relat_1(sK5,sK1) ),
    inference(resolution,[],[f82,f61])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f158,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(sK5,X3)
      | k7_partfun1(X3,sK5,X2) = k1_funct_1(sK5,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK5)) ) ),
    inference(subsumption_resolution,[],[f156,f109])).

fof(f109,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f99,f61])).

fof(f156,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK5))
      | k7_partfun1(X3,sK5,X2) = k1_funct_1(sK5,X2)
      | ~ v5_relat_1(sK5,X3)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f74,f60])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f56,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:58:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (28999)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (28997)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.52  % (29007)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.18/0.52  % (29005)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.18/0.52  % (29016)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.18/0.53  % (29004)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.53  % (29014)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.53  % (28993)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.18/0.53  % (29003)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.53  % (29006)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.53  % (28994)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (29012)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (28998)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.54  % (29013)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.54  % (28996)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.54  % (28992)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (29021)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.55  % (29001)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.55  % (28995)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.55  % (29015)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.55  % (29019)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.55  % (28999)Refutation found. Thanks to Tanya!
% 1.30/0.55  % SZS status Theorem for theBenchmark
% 1.30/0.55  % (29017)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.55  % (29008)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.55  % (29002)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.55  % (29000)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.56  % SZS output start Proof for theBenchmark
% 1.30/0.56  fof(f342,plain,(
% 1.30/0.56    $false),
% 1.30/0.56    inference(subsumption_resolution,[],[f315,f96])).
% 1.30/0.56  fof(f96,plain,(
% 1.30/0.56    v1_xboole_0(k1_xboole_0)),
% 1.30/0.56    inference(resolution,[],[f95,f70])).
% 1.30/0.56  fof(f70,plain,(
% 1.30/0.56    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f48])).
% 1.30/0.56  fof(f48,plain,(
% 1.30/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).
% 1.30/0.56  fof(f47,plain,(
% 1.30/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f46,plain,(
% 1.30/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.56    inference(rectify,[],[f45])).
% 1.30/0.56  fof(f45,plain,(
% 1.30/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.30/0.56    inference(nnf_transformation,[],[f1])).
% 1.30/0.56  fof(f1,axiom,(
% 1.30/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.30/0.56  fof(f95,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.30/0.56    inference(resolution,[],[f78,f66])).
% 1.30/0.56  fof(f66,plain,(
% 1.30/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f4])).
% 1.30/0.56  fof(f4,axiom,(
% 1.30/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.30/0.56  fof(f78,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f30])).
% 1.30/0.56  fof(f30,plain,(
% 1.30/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.30/0.56    inference(ennf_transformation,[],[f9])).
% 1.30/0.56  fof(f9,axiom,(
% 1.30/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.30/0.56  fof(f315,plain,(
% 1.30/0.56    ~v1_xboole_0(k1_xboole_0)),
% 1.30/0.56    inference(backward_demodulation,[],[f56,f314])).
% 1.30/0.56  fof(f314,plain,(
% 1.30/0.56    k1_xboole_0 = sK3),
% 1.30/0.56    inference(global_subsumption,[],[f267,f310])).
% 1.30/0.56  fof(f310,plain,(
% 1.30/0.56    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(backward_demodulation,[],[f65,f309])).
% 1.30/0.56  fof(f309,plain,(
% 1.30/0.56    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(subsumption_resolution,[],[f308,f138])).
% 1.30/0.56  fof(f138,plain,(
% 1.30/0.56    r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))),
% 1.30/0.56    inference(backward_demodulation,[],[f123,f133])).
% 1.30/0.56  fof(f133,plain,(
% 1.30/0.56    k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5)),
% 1.30/0.56    inference(resolution,[],[f81,f61])).
% 1.30/0.56  fof(f61,plain,(
% 1.30/0.56    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f44,plain,(
% 1.30/0.56    (((k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 1.30/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f43,f42,f41,f40])).
% 1.30/0.56  fof(f40,plain,(
% 1.30/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f41,plain,(
% 1.30/0.56    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f42,plain,(
% 1.30/0.56    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(X5,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f43,plain,(
% 1.30/0.56    ? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X5) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(X5,sK2)) => (k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f20,plain,(
% 1.30/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.30/0.56    inference(flattening,[],[f19])).
% 1.30/0.56  fof(f19,plain,(
% 1.30/0.56    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.30/0.56    inference(ennf_transformation,[],[f17])).
% 1.30/0.56  fof(f17,negated_conjecture,(
% 1.30/0.56    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.30/0.56    inference(negated_conjecture,[],[f16])).
% 1.30/0.56  fof(f16,conjecture,(
% 1.30/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 1.30/0.56  fof(f81,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f34])).
% 1.30/0.56  fof(f34,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f11])).
% 1.30/0.56  fof(f11,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.30/0.56  fof(f123,plain,(
% 1.30/0.56    r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5))),
% 1.30/0.56    inference(backward_demodulation,[],[f63,f121])).
% 1.30/0.56  fof(f121,plain,(
% 1.30/0.56    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)),
% 1.30/0.56    inference(resolution,[],[f80,f59])).
% 1.30/0.56  fof(f59,plain,(
% 1.30/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f80,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f33])).
% 1.30/0.56  fof(f33,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f12])).
% 1.30/0.56  fof(f12,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.30/0.56  fof(f63,plain,(
% 1.30/0.56    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f308,plain,(
% 1.30/0.56    ~r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(forward_demodulation,[],[f307,f133])).
% 1.30/0.56  fof(f307,plain,(
% 1.30/0.56    ~r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(subsumption_resolution,[],[f306,f60])).
% 1.30/0.56  fof(f60,plain,(
% 1.30/0.56    v1_funct_1(sK5)),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f306,plain,(
% 1.30/0.56    ~r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) | ~v1_funct_1(sK5) | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(resolution,[],[f252,f61])).
% 1.30/0.56  fof(f252,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),sK6) = k1_funct_1(X1,k1_funct_1(sK4,sK6))) )),
% 1.30/0.56    inference(resolution,[],[f212,f62])).
% 1.30/0.56  fof(f62,plain,(
% 1.30/0.56    m1_subset_1(sK6,sK2)),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f212,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK2) | ~r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))) )),
% 1.30/0.56    inference(forward_demodulation,[],[f211,f121])).
% 1.30/0.56  fof(f211,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) | ~m1_subset_1(X2,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f210,f56])).
% 1.30/0.56  fof(f210,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) | ~m1_subset_1(X2,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) | v1_xboole_0(sK3)) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f209,f57])).
% 1.30/0.56  fof(f57,plain,(
% 1.30/0.56    v1_funct_1(sK4)),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f209,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) | ~m1_subset_1(X2,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) | ~v1_funct_1(sK4) | v1_xboole_0(sK3)) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f208,f59])).
% 1.30/0.56  fof(f208,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) | ~m1_subset_1(X2,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) | ~v1_funct_1(sK4) | v1_xboole_0(sK3)) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f207,f64])).
% 1.30/0.56  fof(f64,plain,(
% 1.30/0.56    k1_xboole_0 != sK2),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f207,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) | ~m1_subset_1(X2,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) | ~v1_funct_1(sK4) | v1_xboole_0(sK3)) )),
% 1.30/0.56    inference(resolution,[],[f79,f58])).
% 1.30/0.56  fof(f58,plain,(
% 1.30/0.56    v1_funct_2(sK4,sK2,sK3)),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f79,plain,(
% 1.30/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X3,X1,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f32])).
% 1.30/0.56  fof(f32,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.30/0.56    inference(flattening,[],[f31])).
% 1.30/0.56  fof(f31,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.30/0.56    inference(ennf_transformation,[],[f15])).
% 1.30/0.56  fof(f15,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 1.30/0.56  fof(f65,plain,(
% 1.30/0.56    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  fof(f267,plain,(
% 1.30/0.56    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) | k1_xboole_0 = sK3),
% 1.30/0.56    inference(subsumption_resolution,[],[f266,f64])).
% 1.30/0.56  fof(f266,plain,(
% 1.30/0.56    k1_xboole_0 = sK3 | k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) | k1_xboole_0 = sK2),
% 1.30/0.56    inference(resolution,[],[f262,f67])).
% 1.30/0.56  fof(f67,plain,(
% 1.30/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.30/0.56    inference(cnf_transformation,[],[f21])).
% 1.30/0.56  fof(f21,plain,(
% 1.30/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.30/0.56    inference(ennf_transformation,[],[f3])).
% 1.30/0.56  fof(f3,axiom,(
% 1.30/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.30/0.56  fof(f262,plain,(
% 1.30/0.56    v1_xboole_0(sK2) | k1_xboole_0 = sK3 | k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))),
% 1.30/0.56    inference(resolution,[],[f190,f100])).
% 1.30/0.56  fof(f100,plain,(
% 1.30/0.56    r2_hidden(sK6,sK2) | v1_xboole_0(sK2)),
% 1.30/0.56    inference(resolution,[],[f72,f62])).
% 1.30/0.56  fof(f72,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f24])).
% 1.30/0.56  fof(f24,plain,(
% 1.30/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.30/0.56    inference(flattening,[],[f23])).
% 1.30/0.56  fof(f23,plain,(
% 1.30/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.30/0.56    inference(ennf_transformation,[],[f5])).
% 1.30/0.56  fof(f5,axiom,(
% 1.30/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.30/0.56  fof(f190,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_funct_1(sK5,k1_funct_1(sK4,X0)) = k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) | k1_xboole_0 = sK3) )),
% 1.30/0.56    inference(superposition,[],[f173,f150])).
% 1.30/0.56  fof(f150,plain,(
% 1.30/0.56    sK2 = k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 1.30/0.56    inference(superposition,[],[f149,f132])).
% 1.30/0.56  fof(f132,plain,(
% 1.30/0.56    k1_relat_1(sK4) = k1_relset_1(sK2,sK3,sK4)),
% 1.30/0.56    inference(resolution,[],[f81,f59])).
% 1.30/0.56  fof(f149,plain,(
% 1.30/0.56    sK2 = k1_relset_1(sK2,sK3,sK4) | k1_xboole_0 = sK3),
% 1.30/0.56    inference(subsumption_resolution,[],[f148,f117])).
% 1.30/0.56  fof(f117,plain,(
% 1.30/0.56    sP0(sK2,sK4,sK3)),
% 1.30/0.56    inference(resolution,[],[f87,f59])).
% 1.30/0.56  fof(f87,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f55])).
% 1.30/0.56  fof(f55,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(nnf_transformation,[],[f39])).
% 1.30/0.56  fof(f39,plain,(
% 1.30/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(definition_folding,[],[f37,f38])).
% 1.30/0.56  fof(f38,plain,(
% 1.30/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.30/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.56  % (29018)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.56  fof(f37,plain,(
% 1.30/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(flattening,[],[f36])).
% 1.30/0.56  fof(f36,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f13])).
% 1.30/0.56  fof(f13,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.30/0.56  fof(f148,plain,(
% 1.30/0.56    sK2 = k1_relset_1(sK2,sK3,sK4) | k1_xboole_0 = sK3 | ~sP0(sK2,sK4,sK3)),
% 1.30/0.56    inference(resolution,[],[f83,f58])).
% 1.30/0.56  fof(f83,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f54])).
% 1.30/0.56  fof(f54,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.30/0.56    inference(rectify,[],[f53])).
% 1.30/0.56  fof(f53,plain,(
% 1.30/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.30/0.56    inference(nnf_transformation,[],[f38])).
% 1.30/0.56  fof(f173,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK5,k1_funct_1(sK4,X0)) = k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0))) )),
% 1.30/0.56    inference(resolution,[],[f172,f147])).
% 1.30/0.56  fof(f147,plain,(
% 1.30/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) | ~r2_hidden(X0,k1_relat_1(sK4))) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f146,f108])).
% 1.30/0.56  fof(f108,plain,(
% 1.30/0.56    v1_relat_1(sK4)),
% 1.30/0.56    inference(resolution,[],[f99,f59])).
% 1.30/0.56  fof(f99,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.30/0.56    inference(resolution,[],[f68,f71])).
% 1.30/0.56  fof(f71,plain,(
% 1.30/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.30/0.56    inference(cnf_transformation,[],[f7])).
% 1.30/0.56  fof(f7,axiom,(
% 1.30/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.30/0.56  fof(f68,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f22])).
% 1.30/0.56  fof(f22,plain,(
% 1.30/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.56    inference(ennf_transformation,[],[f6])).
% 1.30/0.56  fof(f6,axiom,(
% 1.30/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.30/0.56  fof(f146,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5))) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f145,f57])).
% 1.30/0.56  fof(f145,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5))) )),
% 1.30/0.56    inference(resolution,[],[f73,f136])).
% 1.30/0.56  fof(f136,plain,(
% 1.30/0.56    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(sK4)) | r2_hidden(X4,k1_relat_1(sK5))) )),
% 1.30/0.56    inference(backward_demodulation,[],[f125,f133])).
% 1.30/0.56  fof(f125,plain,(
% 1.30/0.56    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(sK4)) | r2_hidden(X4,k1_relset_1(sK3,sK1,sK5))) )),
% 1.30/0.56    inference(backward_demodulation,[],[f114,f121])).
% 1.30/0.56  fof(f114,plain,(
% 1.30/0.56    ( ! [X4] : (~r2_hidden(X4,k2_relset_1(sK2,sK3,sK4)) | r2_hidden(X4,k1_relset_1(sK3,sK1,sK5))) )),
% 1.30/0.56    inference(resolution,[],[f75,f63])).
% 1.30/0.56  fof(f75,plain,(
% 1.30/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f52])).
% 1.30/0.56  fof(f52,plain,(
% 1.30/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).
% 1.30/0.56  fof(f51,plain,(
% 1.30/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.30/0.56    introduced(choice_axiom,[])).
% 1.30/0.56  fof(f50,plain,(
% 1.30/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.56    inference(rectify,[],[f49])).
% 1.30/0.56  % (29020)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.56  fof(f49,plain,(
% 1.30/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.30/0.56    inference(nnf_transformation,[],[f29])).
% 1.30/0.56  fof(f29,plain,(
% 1.30/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.30/0.56    inference(ennf_transformation,[],[f2])).
% 1.30/0.56  fof(f2,axiom,(
% 1.30/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.56  fof(f73,plain,(
% 1.30/0.56    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f26])).
% 1.30/0.56  fof(f26,plain,(
% 1.30/0.56    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.30/0.56    inference(flattening,[],[f25])).
% 1.30/0.56  fof(f25,plain,(
% 1.30/0.56    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.30/0.56    inference(ennf_transformation,[],[f8])).
% 1.30/0.56  fof(f8,axiom,(
% 1.30/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.30/0.56  fof(f172,plain,(
% 1.30/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK5)) | k1_funct_1(sK5,X0) = k7_partfun1(sK1,sK5,X0)) )),
% 1.30/0.56    inference(resolution,[],[f158,f116])).
% 1.30/0.56  fof(f116,plain,(
% 1.30/0.56    v5_relat_1(sK5,sK1)),
% 1.30/0.56    inference(resolution,[],[f82,f61])).
% 1.30/0.56  fof(f82,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f35])).
% 1.30/0.56  fof(f35,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.56    inference(ennf_transformation,[],[f18])).
% 1.30/0.56  fof(f18,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.30/0.56    inference(pure_predicate_removal,[],[f10])).
% 1.30/0.56  fof(f10,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.30/0.56  fof(f158,plain,(
% 1.30/0.56    ( ! [X2,X3] : (~v5_relat_1(sK5,X3) | k7_partfun1(X3,sK5,X2) = k1_funct_1(sK5,X2) | ~r2_hidden(X2,k1_relat_1(sK5))) )),
% 1.30/0.56    inference(subsumption_resolution,[],[f156,f109])).
% 1.30/0.56  fof(f109,plain,(
% 1.30/0.56    v1_relat_1(sK5)),
% 1.30/0.56    inference(resolution,[],[f99,f61])).
% 1.30/0.56  fof(f156,plain,(
% 1.30/0.56    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK5)) | k7_partfun1(X3,sK5,X2) = k1_funct_1(sK5,X2) | ~v5_relat_1(sK5,X3) | ~v1_relat_1(sK5)) )),
% 1.30/0.56    inference(resolution,[],[f74,f60])).
% 1.30/0.56  fof(f74,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f28])).
% 1.30/0.56  fof(f28,plain,(
% 1.30/0.56    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.56    inference(flattening,[],[f27])).
% 1.30/0.56  fof(f27,plain,(
% 1.30/0.56    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.30/0.56    inference(ennf_transformation,[],[f14])).
% 1.30/0.56  fof(f14,axiom,(
% 1.30/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.30/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 1.30/0.56  fof(f56,plain,(
% 1.30/0.56    ~v1_xboole_0(sK3)),
% 1.30/0.56    inference(cnf_transformation,[],[f44])).
% 1.30/0.56  % SZS output end Proof for theBenchmark
% 1.30/0.56  % (28999)------------------------------
% 1.30/0.56  % (28999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (28999)Termination reason: Refutation
% 1.30/0.56  
% 1.30/0.56  % (28999)Memory used [KB]: 6652
% 1.30/0.56  % (28999)Time elapsed: 0.120 s
% 1.30/0.56  % (28999)------------------------------
% 1.30/0.56  % (28999)------------------------------
% 1.30/0.56  % (29011)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.56  % (29009)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.56  % (28991)Success in time 0.196 s
%------------------------------------------------------------------------------
