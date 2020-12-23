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
% DateTime   : Thu Dec  3 13:07:45 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 526 expanded)
%              Number of leaves         :   38 ( 228 expanded)
%              Depth                    :   12
%              Number of atoms          :  624 (4220 expanded)
%              Number of equality atoms :  104 ( 957 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2681,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f274,f591,f601,f725,f733,f829,f1067,f1122,f1190,f1192,f1349,f1387,f1401,f1403,f1543,f1613,f1635,f2674,f2680])).

fof(f2680,plain,
    ( ~ spl8_2
    | ~ spl8_103 ),
    inference(avatar_contradiction_clause,[],[f2679])).

fof(f2679,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_103 ),
    inference(subsumption_resolution,[],[f2678,f2675])).

fof(f2675,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl8_2
    | ~ spl8_103 ),
    inference(resolution,[],[f128,f2019])).

fof(f2019,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl8_103 ),
    inference(resolution,[],[f1634,f195])).

fof(f195,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(resolution,[],[f71,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f50,f49,f48,f47])).

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f1634,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK4,X1)
        | ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f1633,plain,
    ( spl8_103
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v5_relat_1(sK4,X1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f128,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_2
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2678,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f75,f604])).

fof(f604,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f255,f72])).

fof(f72,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f255,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(global_subsumption,[],[f66,f67,f70,f74,f68,f69,f71,f252])).

fof(f252,plain,(
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
    inference(resolution,[],[f73,f101])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f73,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f2674,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f2672,f127,f124])).

fof(f124,plain,
    ( spl8_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2672,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f72,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1635,plain,
    ( ~ spl8_68
    | ~ spl8_69
    | spl8_103
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f1630,f1317,f1633,f718,f715])).

fof(f715,plain,
    ( spl8_68
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f718,plain,
    ( spl8_69
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f1317,plain,
    ( spl8_91
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f1630,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0))
        | ~ v1_funct_1(sK4)
        | ~ v5_relat_1(sK4,X1)
        | ~ v1_relat_1(sK4) )
    | ~ spl8_91 ),
    inference(resolution,[],[f1318,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f1318,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_91 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f1613,plain,
    ( spl8_67
    | spl8_91
    | ~ spl8_92
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f1609,f550,f1320,f1317,f643])).

fof(f643,plain,
    ( spl8_67
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f1320,plain,
    ( spl8_92
  <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f550,plain,
    ( spl8_54
  <=> ! [X7,X6] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X6)
        | ~ v1_funct_2(sK3,sK1,X6)
        | ~ r2_hidden(X7,sK1)
        | r2_hidden(k1_funct_1(sK3,X7),X6)
        | k1_xboole_0 = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f1609,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
        | k1_xboole_0 = k1_relat_1(sK4) )
    | ~ spl8_54 ),
    inference(resolution,[],[f551,f477])).

fof(f477,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f73,f194])).

fof(f194,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f71,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f551,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X6)
        | ~ v1_funct_2(sK3,sK1,X6)
        | ~ r2_hidden(X7,sK1)
        | r2_hidden(k1_funct_1(sK3,X7),X6)
        | k1_xboole_0 = X6 )
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f550])).

fof(f1543,plain,
    ( ~ spl8_35
    | spl8_54
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f1533,f170,f550,f387])).

fof(f387,plain,
    ( spl8_35
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f170,plain,
    ( spl8_8
  <=> ! [X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1533,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X6)
        | k1_xboole_0 = X6
        | ~ r2_hidden(X7,sK1)
        | r2_hidden(k1_funct_1(sK3,X7),X6)
        | ~ v1_funct_2(sK3,sK1,X6)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f171,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f171,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f1403,plain,(
    spl8_27 ),
    inference(avatar_contradiction_clause,[],[f1402])).

fof(f1402,plain,
    ( $false
    | spl8_27 ),
    inference(subsumption_resolution,[],[f76,f355])).

fof(f355,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl8_27
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1401,plain,
    ( ~ spl8_59
    | spl8_60
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f878,f170,f573,f570])).

fof(f570,plain,
    ( spl8_59
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f573,plain,
    ( spl8_60
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f878,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl8_8 ),
    inference(superposition,[],[f171,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1387,plain,
    ( spl8_59
    | ~ spl8_67 ),
    inference(avatar_contradiction_clause,[],[f1373])).

fof(f1373,plain,
    ( $false
    | spl8_59
    | ~ spl8_67 ),
    inference(subsumption_resolution,[],[f571,f1351])).

fof(f1351,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl8_67 ),
    inference(backward_demodulation,[],[f477,f644])).

fof(f644,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f643])).

fof(f571,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | spl8_59 ),
    inference(avatar_component_clause,[],[f570])).

fof(f1349,plain,
    ( ~ spl8_7
    | spl8_92 ),
    inference(avatar_contradiction_clause,[],[f1347])).

fof(f1347,plain,
    ( $false
    | ~ spl8_7
    | spl8_92 ),
    inference(subsumption_resolution,[],[f518,f1321])).

fof(f1321,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | spl8_92 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f518,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl8_7 ),
    inference(resolution,[],[f166,f477])).

fof(f166,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | v1_funct_2(sK3,sK1,X1) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_7
  <=> ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | v1_funct_2(sK3,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1192,plain,
    ( spl8_8
    | spl8_6 ),
    inference(avatar_split_clause,[],[f1191,f160,f170])).

fof(f160,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1191,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(global_subsumption,[],[f802])).

fof(f802,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(global_subsumption,[],[f680])).

fof(f680,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(global_subsumption,[],[f67,f68,f672])).

fof(f672,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f69,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f1190,plain,
    ( spl8_7
    | spl8_6 ),
    inference(avatar_split_clause,[],[f1189,f160,f165])).

fof(f1189,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(global_subsumption,[],[f800])).

fof(f800,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(global_subsumption,[],[f678])).

fof(f678,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1) ) ),
    inference(global_subsumption,[],[f67,f68,f671])).

fof(f671,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | v1_funct_2(sK3,sK1,X1)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f69,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1122,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f1074])).

fof(f1074,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f74,f1068])).

fof(f1068,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_1 ),
    inference(resolution,[],[f125,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f125,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1067,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f1066,f152,f124])).

fof(f152,plain,
    ( spl8_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1066,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f1063])).

fof(f1063,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f585])).

fof(f585,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f150])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f66,f67,f68,f138])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f69,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f829,plain,
    ( spl8_9
    | ~ spl8_27
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f824,f573,f354,f174])).

fof(f174,plain,
    ( spl8_9
  <=> ! [X3] : ~ r2_hidden(X3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f824,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_60 ),
    inference(resolution,[],[f574,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f574,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f573])).

fof(f733,plain,(
    spl8_69 ),
    inference(avatar_contradiction_clause,[],[f732])).

fof(f732,plain,
    ( $false
    | spl8_69 ),
    inference(subsumption_resolution,[],[f70,f719])).

fof(f719,plain,
    ( ~ v1_funct_1(sK4)
    | spl8_69 ),
    inference(avatar_component_clause,[],[f718])).

fof(f725,plain,(
    spl8_68 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | spl8_68 ),
    inference(subsumption_resolution,[],[f193,f716])).

fof(f716,plain,
    ( ~ v1_relat_1(sK4)
    | spl8_68 ),
    inference(avatar_component_clause,[],[f715])).

fof(f193,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f71,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f601,plain,
    ( spl8_4
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f153,f592])).

fof(f592,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_9 ),
    inference(resolution,[],[f175,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f175,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f153,plain,
    ( ~ v1_xboole_0(sK3)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f591,plain,(
    spl8_35 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | spl8_35 ),
    inference(subsumption_resolution,[],[f67,f388])).

fof(f388,plain,
    ( ~ v1_funct_1(sK3)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f387])).

fof(f274,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f76,f264])).

fof(f264,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f66,f161])).

fof(f161,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (14816)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (14833)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (14830)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (14806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (14815)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (14818)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (14805)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (14835)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.56  % (14808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.56  % (14826)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.56  % (14812)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.56  % (14822)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.57  % (14823)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.57  % (14814)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.57  % (14809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.57  % (14817)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.57  % (14825)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.57  % (14820)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.57  % (14804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.57  % (14829)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.57  % (14807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.57  % (14834)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.57  % (14824)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.57  % (14819)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.58  % (14828)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.58  % (14827)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.58  % (14832)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.58  % (14810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.58  % (14821)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.64/0.59  % (14836)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.01/0.63  % (14828)Refutation not found, incomplete strategy% (14828)------------------------------
% 2.01/0.63  % (14828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (14828)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.63  
% 2.01/0.63  % (14828)Memory used [KB]: 11129
% 2.01/0.63  % (14828)Time elapsed: 0.200 s
% 2.01/0.63  % (14828)------------------------------
% 2.01/0.63  % (14828)------------------------------
% 2.15/0.68  % (14806)Refutation found. Thanks to Tanya!
% 2.15/0.68  % SZS status Theorem for theBenchmark
% 2.15/0.68  % SZS output start Proof for theBenchmark
% 2.15/0.70  fof(f2681,plain,(
% 2.15/0.70    $false),
% 2.15/0.70    inference(avatar_sat_refutation,[],[f274,f591,f601,f725,f733,f829,f1067,f1122,f1190,f1192,f1349,f1387,f1401,f1403,f1543,f1613,f1635,f2674,f2680])).
% 2.15/0.70  fof(f2680,plain,(
% 2.15/0.70    ~spl8_2 | ~spl8_103),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f2679])).
% 2.15/0.70  fof(f2679,plain,(
% 2.15/0.70    $false | (~spl8_2 | ~spl8_103)),
% 2.15/0.70    inference(subsumption_resolution,[],[f2678,f2675])).
% 2.15/0.70  fof(f2675,plain,(
% 2.15/0.70    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl8_2 | ~spl8_103)),
% 2.15/0.70    inference(resolution,[],[f128,f2019])).
% 2.15/0.70  fof(f2019,plain,(
% 2.15/0.70    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0))) ) | ~spl8_103),
% 2.15/0.70    inference(resolution,[],[f1634,f195])).
% 2.15/0.70  fof(f195,plain,(
% 2.15/0.70    v5_relat_1(sK4,sK0)),
% 2.15/0.70    inference(resolution,[],[f71,f104])).
% 2.15/0.70  fof(f104,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f39])).
% 2.15/0.70  fof(f39,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.70    inference(ennf_transformation,[],[f23])).
% 2.15/0.70  fof(f23,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.15/0.70    inference(pure_predicate_removal,[],[f12])).
% 2.15/0.70  fof(f12,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.15/0.70  fof(f71,plain,(
% 2.15/0.70    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f51,plain,(
% 2.15/0.70    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.15/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f50,f49,f48,f47])).
% 2.15/0.70  fof(f47,plain,(
% 2.15/0.70    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f48,plain,(
% 2.15/0.70    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f49,plain,(
% 2.15/0.70    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f50,plain,(
% 2.15/0.70    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f25,plain,(
% 2.15/0.70    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.15/0.70    inference(flattening,[],[f24])).
% 2.15/0.70  fof(f24,plain,(
% 2.15/0.70    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.15/0.70    inference(ennf_transformation,[],[f22])).
% 2.15/0.70  fof(f22,negated_conjecture,(
% 2.15/0.70    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.15/0.70    inference(negated_conjecture,[],[f21])).
% 2.15/0.70  fof(f21,conjecture,(
% 2.15/0.70    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 2.15/0.70  fof(f1634,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v5_relat_1(sK4,X1) | ~r2_hidden(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0))) ) | ~spl8_103),
% 2.15/0.70    inference(avatar_component_clause,[],[f1633])).
% 2.15/0.70  fof(f1633,plain,(
% 2.15/0.70    spl8_103 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | ~v5_relat_1(sK4,X1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 2.15/0.70  fof(f128,plain,(
% 2.15/0.70    r2_hidden(sK5,sK1) | ~spl8_2),
% 2.15/0.70    inference(avatar_component_clause,[],[f127])).
% 2.15/0.70  fof(f127,plain,(
% 2.15/0.70    spl8_2 <=> r2_hidden(sK5,sK1)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.15/0.70  fof(f2678,plain,(
% 2.15/0.70    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 2.15/0.70    inference(backward_demodulation,[],[f75,f604])).
% 2.15/0.70  fof(f604,plain,(
% 2.15/0.70    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 2.15/0.70    inference(resolution,[],[f255,f72])).
% 2.15/0.70  fof(f72,plain,(
% 2.15/0.70    m1_subset_1(sK5,sK1)),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f255,plain,(
% 2.15/0.70    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.15/0.70    inference(global_subsumption,[],[f66,f67,f70,f74,f68,f69,f71,f252])).
% 2.15/0.70  fof(f252,plain,(
% 2.15/0.70    ( ! [X0] : (k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) )),
% 2.15/0.70    inference(resolution,[],[f73,f101])).
% 2.15/0.70  fof(f101,plain,(
% 2.15/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f36])).
% 2.15/0.70  fof(f36,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.15/0.70    inference(flattening,[],[f35])).
% 2.15/0.70  fof(f35,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.15/0.70    inference(ennf_transformation,[],[f18])).
% 2.15/0.70  fof(f18,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 2.15/0.70  fof(f73,plain,(
% 2.15/0.70    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f69,plain,(
% 2.15/0.70    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f68,plain,(
% 2.15/0.70    v1_funct_2(sK3,sK1,sK2)),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f74,plain,(
% 2.15/0.70    k1_xboole_0 != sK1),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f70,plain,(
% 2.15/0.70    v1_funct_1(sK4)),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f67,plain,(
% 2.15/0.70    v1_funct_1(sK3)),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f66,plain,(
% 2.15/0.70    ~v1_xboole_0(sK2)),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f75,plain,(
% 2.15/0.70    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 2.15/0.70    inference(cnf_transformation,[],[f51])).
% 2.15/0.70  fof(f2674,plain,(
% 2.15/0.70    spl8_1 | spl8_2),
% 2.15/0.70    inference(avatar_split_clause,[],[f2672,f127,f124])).
% 2.15/0.70  fof(f124,plain,(
% 2.15/0.70    spl8_1 <=> v1_xboole_0(sK1)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.15/0.70  fof(f2672,plain,(
% 2.15/0.70    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 2.15/0.70    inference(resolution,[],[f72,f80])).
% 2.15/0.70  fof(f80,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f56])).
% 2.15/0.70  fof(f56,plain,(
% 2.15/0.70    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.15/0.70    inference(nnf_transformation,[],[f27])).
% 2.15/0.70  fof(f27,plain,(
% 2.15/0.70    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.15/0.70    inference(ennf_transformation,[],[f7])).
% 2.15/0.70  fof(f7,axiom,(
% 2.15/0.70    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.15/0.70  fof(f1635,plain,(
% 2.15/0.70    ~spl8_68 | ~spl8_69 | spl8_103 | ~spl8_91),
% 2.15/0.70    inference(avatar_split_clause,[],[f1630,f1317,f1633,f718,f715])).
% 2.15/0.70  fof(f715,plain,(
% 2.15/0.70    spl8_68 <=> v1_relat_1(sK4)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 2.15/0.70  fof(f718,plain,(
% 2.15/0.70    spl8_69 <=> v1_funct_1(sK4)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).
% 2.15/0.70  fof(f1317,plain,(
% 2.15/0.70    spl8_91 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).
% 2.15/0.70  fof(f1630,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = k7_partfun1(X1,sK4,k1_funct_1(sK3,X0)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) ) | ~spl8_91),
% 2.15/0.70    inference(resolution,[],[f1318,f89])).
% 2.15/0.70  fof(f89,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f33])).
% 2.15/0.70  fof(f33,plain,(
% 2.15/0.70    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(flattening,[],[f32])).
% 2.15/0.70  fof(f32,plain,(
% 2.15/0.70    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.15/0.70    inference(ennf_transformation,[],[f17])).
% 2.15/0.70  fof(f17,axiom,(
% 2.15/0.70    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 2.15/0.70  fof(f1318,plain,(
% 2.15/0.70    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | ~r2_hidden(X0,sK1)) ) | ~spl8_91),
% 2.15/0.70    inference(avatar_component_clause,[],[f1317])).
% 2.15/0.70  fof(f1613,plain,(
% 2.15/0.70    spl8_67 | spl8_91 | ~spl8_92 | ~spl8_54),
% 2.15/0.70    inference(avatar_split_clause,[],[f1609,f550,f1320,f1317,f643])).
% 2.15/0.70  fof(f643,plain,(
% 2.15/0.70    spl8_67 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 2.15/0.70  fof(f1320,plain,(
% 2.15/0.70    spl8_92 <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 2.15/0.70  fof(f550,plain,(
% 2.15/0.70    spl8_54 <=> ! [X7,X6] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X6) | ~v1_funct_2(sK3,sK1,X6) | ~r2_hidden(X7,sK1) | r2_hidden(k1_funct_1(sK3,X7),X6) | k1_xboole_0 = X6)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 2.15/0.70  fof(f1609,plain,(
% 2.15/0.70    ( ! [X0] : (~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | k1_xboole_0 = k1_relat_1(sK4)) ) | ~spl8_54),
% 2.15/0.70    inference(resolution,[],[f551,f477])).
% 2.15/0.70  fof(f477,plain,(
% 2.15/0.70    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 2.15/0.70    inference(backward_demodulation,[],[f73,f194])).
% 2.15/0.70  fof(f194,plain,(
% 2.15/0.70    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 2.15/0.70    inference(resolution,[],[f71,f103])).
% 2.15/0.70  fof(f103,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f38])).
% 2.15/0.70  fof(f38,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.70    inference(ennf_transformation,[],[f15])).
% 2.15/0.70  fof(f15,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.15/0.70  fof(f551,plain,(
% 2.15/0.70    ( ! [X6,X7] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X6) | ~v1_funct_2(sK3,sK1,X6) | ~r2_hidden(X7,sK1) | r2_hidden(k1_funct_1(sK3,X7),X6) | k1_xboole_0 = X6) ) | ~spl8_54),
% 2.15/0.70    inference(avatar_component_clause,[],[f550])).
% 2.15/0.70  fof(f1543,plain,(
% 2.15/0.70    ~spl8_35 | spl8_54 | ~spl8_8),
% 2.15/0.70    inference(avatar_split_clause,[],[f1533,f170,f550,f387])).
% 2.15/0.70  fof(f387,plain,(
% 2.15/0.70    spl8_35 <=> v1_funct_1(sK3)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 2.15/0.70  fof(f170,plain,(
% 2.15/0.70    spl8_8 <=> ! [X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.15/0.70  fof(f1533,plain,(
% 2.15/0.70    ( ! [X6,X7] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X6) | k1_xboole_0 = X6 | ~r2_hidden(X7,sK1) | r2_hidden(k1_funct_1(sK3,X7),X6) | ~v1_funct_2(sK3,sK1,X6) | ~v1_funct_1(sK3)) ) | ~spl8_8),
% 2.15/0.70    inference(resolution,[],[f171,f107])).
% 2.15/0.70  fof(f107,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f44])).
% 2.15/0.70  fof(f44,plain,(
% 2.15/0.70    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.15/0.70    inference(flattening,[],[f43])).
% 2.15/0.70  fof(f43,plain,(
% 2.15/0.70    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.15/0.70    inference(ennf_transformation,[],[f19])).
% 2.15/0.70  fof(f19,axiom,(
% 2.15/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 2.15/0.70  fof(f171,plain,(
% 2.15/0.70    ( ! [X2] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)) ) | ~spl8_8),
% 2.15/0.70    inference(avatar_component_clause,[],[f170])).
% 2.15/0.70  fof(f1403,plain,(
% 2.15/0.70    spl8_27),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f1402])).
% 2.15/0.70  fof(f1402,plain,(
% 2.15/0.70    $false | spl8_27),
% 2.15/0.70    inference(subsumption_resolution,[],[f76,f355])).
% 2.15/0.70  fof(f355,plain,(
% 2.15/0.70    ~v1_xboole_0(k1_xboole_0) | spl8_27),
% 2.15/0.70    inference(avatar_component_clause,[],[f354])).
% 2.15/0.70  fof(f354,plain,(
% 2.15/0.70    spl8_27 <=> v1_xboole_0(k1_xboole_0)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 2.15/0.70  fof(f76,plain,(
% 2.15/0.70    v1_xboole_0(k1_xboole_0)),
% 2.15/0.70    inference(cnf_transformation,[],[f3])).
% 2.15/0.70  fof(f3,axiom,(
% 2.15/0.70    v1_xboole_0(k1_xboole_0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.15/0.70  fof(f1401,plain,(
% 2.15/0.70    ~spl8_59 | spl8_60 | ~spl8_8),
% 2.15/0.70    inference(avatar_split_clause,[],[f878,f170,f573,f570])).
% 2.15/0.70  fof(f570,plain,(
% 2.15/0.70    spl8_59 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 2.15/0.70  fof(f573,plain,(
% 2.15/0.70    spl8_60 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 2.15/0.70  fof(f878,plain,(
% 2.15/0.70    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | ~spl8_8),
% 2.15/0.70    inference(superposition,[],[f171,f116])).
% 2.15/0.70  fof(f116,plain,(
% 2.15/0.70    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.15/0.70    inference(equality_resolution,[],[f100])).
% 2.15/0.70  fof(f100,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.15/0.70    inference(cnf_transformation,[],[f65])).
% 2.15/0.70  fof(f65,plain,(
% 2.15/0.70    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.15/0.70    inference(flattening,[],[f64])).
% 2.15/0.70  fof(f64,plain,(
% 2.15/0.70    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.15/0.70    inference(nnf_transformation,[],[f6])).
% 2.15/0.70  fof(f6,axiom,(
% 2.15/0.70    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.15/0.70  fof(f1387,plain,(
% 2.15/0.70    spl8_59 | ~spl8_67),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f1373])).
% 2.15/0.70  fof(f1373,plain,(
% 2.15/0.70    $false | (spl8_59 | ~spl8_67)),
% 2.15/0.70    inference(subsumption_resolution,[],[f571,f1351])).
% 2.15/0.70  fof(f1351,plain,(
% 2.15/0.70    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | ~spl8_67),
% 2.15/0.70    inference(backward_demodulation,[],[f477,f644])).
% 2.15/0.70  fof(f644,plain,(
% 2.15/0.70    k1_xboole_0 = k1_relat_1(sK4) | ~spl8_67),
% 2.15/0.70    inference(avatar_component_clause,[],[f643])).
% 2.15/0.70  fof(f571,plain,(
% 2.15/0.70    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | spl8_59),
% 2.15/0.70    inference(avatar_component_clause,[],[f570])).
% 2.15/0.70  fof(f1349,plain,(
% 2.15/0.70    ~spl8_7 | spl8_92),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f1347])).
% 2.15/0.70  fof(f1347,plain,(
% 2.15/0.70    $false | (~spl8_7 | spl8_92)),
% 2.15/0.70    inference(subsumption_resolution,[],[f518,f1321])).
% 2.15/0.70  fof(f1321,plain,(
% 2.15/0.70    ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | spl8_92),
% 2.15/0.70    inference(avatar_component_clause,[],[f1320])).
% 2.15/0.70  fof(f518,plain,(
% 2.15/0.70    v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~spl8_7),
% 2.15/0.70    inference(resolution,[],[f166,f477])).
% 2.15/0.70  fof(f166,plain,(
% 2.15/0.70    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1)) ) | ~spl8_7),
% 2.15/0.70    inference(avatar_component_clause,[],[f165])).
% 2.15/0.70  fof(f165,plain,(
% 2.15/0.70    spl8_7 <=> ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.15/0.70  fof(f1192,plain,(
% 2.15/0.70    spl8_8 | spl8_6),
% 2.15/0.70    inference(avatar_split_clause,[],[f1191,f160,f170])).
% 2.15/0.70  fof(f160,plain,(
% 2.15/0.70    spl8_6 <=> k1_xboole_0 = sK2),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.15/0.70  fof(f1191,plain,(
% 2.15/0.70    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 2.15/0.70    inference(global_subsumption,[],[f802])).
% 2.15/0.70  fof(f802,plain,(
% 2.15/0.70    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 2.15/0.70    inference(global_subsumption,[],[f680])).
% 2.15/0.70  fof(f680,plain,(
% 2.15/0.70    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 2.15/0.70    inference(global_subsumption,[],[f67,f68,f672])).
% 2.15/0.70  fof(f672,plain,(
% 2.15/0.70    ( ! [X2] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) )),
% 2.15/0.70    inference(resolution,[],[f69,f112])).
% 2.15/0.70  fof(f112,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f46])).
% 2.15/0.70  fof(f46,plain,(
% 2.15/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.15/0.70    inference(flattening,[],[f45])).
% 2.15/0.70  fof(f45,plain,(
% 2.15/0.70    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.15/0.70    inference(ennf_transformation,[],[f20])).
% 2.15/0.70  fof(f20,axiom,(
% 2.15/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 2.15/0.70  fof(f1190,plain,(
% 2.15/0.70    spl8_7 | spl8_6),
% 2.15/0.70    inference(avatar_split_clause,[],[f1189,f160,f165])).
% 2.15/0.70  fof(f1189,plain,(
% 2.15/0.70    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1)) )),
% 2.15/0.70    inference(global_subsumption,[],[f800])).
% 2.15/0.70  fof(f800,plain,(
% 2.15/0.70    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1)) )),
% 2.15/0.70    inference(global_subsumption,[],[f678])).
% 2.15/0.70  fof(f678,plain,(
% 2.15/0.70    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1)) )),
% 2.15/0.70    inference(global_subsumption,[],[f67,f68,f671])).
% 2.15/0.70  fof(f671,plain,(
% 2.15/0.70    ( ! [X1] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | v1_funct_2(sK3,sK1,X1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3)) )),
% 2.15/0.70    inference(resolution,[],[f69,f110])).
% 2.15/0.70  fof(f110,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f46])).
% 2.15/0.70  fof(f1122,plain,(
% 2.15/0.70    ~spl8_1),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f1074])).
% 2.15/0.70  fof(f1074,plain,(
% 2.15/0.70    $false | ~spl8_1),
% 2.15/0.70    inference(subsumption_resolution,[],[f74,f1068])).
% 2.15/0.70  fof(f1068,plain,(
% 2.15/0.70    k1_xboole_0 = sK1 | ~spl8_1),
% 2.15/0.70    inference(resolution,[],[f125,f77])).
% 2.15/0.70  fof(f77,plain,(
% 2.15/0.70    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f26])).
% 2.15/0.70  fof(f26,plain,(
% 2.15/0.70    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.15/0.70    inference(ennf_transformation,[],[f4])).
% 2.15/0.70  fof(f4,axiom,(
% 2.15/0.70    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.15/0.70  fof(f125,plain,(
% 2.15/0.70    v1_xboole_0(sK1) | ~spl8_1),
% 2.15/0.70    inference(avatar_component_clause,[],[f124])).
% 2.15/0.70  fof(f1067,plain,(
% 2.15/0.70    spl8_1 | ~spl8_4),
% 2.15/0.70    inference(avatar_split_clause,[],[f1066,f152,f124])).
% 2.15/0.70  fof(f152,plain,(
% 2.15/0.70    spl8_4 <=> v1_xboole_0(sK3)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.15/0.70  fof(f1066,plain,(
% 2.15/0.70    ~v1_xboole_0(sK3) | v1_xboole_0(sK1)),
% 2.15/0.70    inference(global_subsumption,[],[f1063])).
% 2.15/0.70  fof(f1063,plain,(
% 2.15/0.70    ~v1_xboole_0(sK3) | v1_xboole_0(sK1)),
% 2.15/0.70    inference(global_subsumption,[],[f585])).
% 2.15/0.70  fof(f585,plain,(
% 2.15/0.70    ~v1_xboole_0(sK3) | v1_xboole_0(sK1)),
% 2.15/0.70    inference(global_subsumption,[],[f150])).
% 2.15/0.70  fof(f150,plain,(
% 2.15/0.70    ~v1_xboole_0(sK3) | v1_xboole_0(sK1)),
% 2.15/0.70    inference(global_subsumption,[],[f66,f67,f68,f138])).
% 2.15/0.70  fof(f138,plain,(
% 2.15/0.70    ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~v1_xboole_0(sK3) | v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 2.15/0.70    inference(resolution,[],[f69,f87])).
% 2.15/0.70  fof(f87,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f31])).
% 2.15/0.70  fof(f31,plain,(
% 2.15/0.70    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.15/0.70    inference(flattening,[],[f30])).
% 2.15/0.70  fof(f30,plain,(
% 2.15/0.70    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.15/0.70    inference(ennf_transformation,[],[f16])).
% 2.15/0.70  fof(f16,axiom,(
% 2.15/0.70    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).
% 2.15/0.70  fof(f829,plain,(
% 2.15/0.70    spl8_9 | ~spl8_27 | ~spl8_60),
% 2.15/0.70    inference(avatar_split_clause,[],[f824,f573,f354,f174])).
% 2.15/0.70  fof(f174,plain,(
% 2.15/0.70    spl8_9 <=> ! [X3] : ~r2_hidden(X3,sK3)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.15/0.70  fof(f824,plain,(
% 2.15/0.70    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,sK3)) ) | ~spl8_60),
% 2.15/0.70    inference(resolution,[],[f574,f106])).
% 2.15/0.70  fof(f106,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f42])).
% 2.15/0.70  fof(f42,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f10])).
% 2.15/0.70  fof(f10,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.15/0.70  fof(f574,plain,(
% 2.15/0.70    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_60),
% 2.15/0.70    inference(avatar_component_clause,[],[f573])).
% 2.15/0.70  fof(f733,plain,(
% 2.15/0.70    spl8_69),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f732])).
% 2.15/0.70  fof(f732,plain,(
% 2.15/0.70    $false | spl8_69),
% 2.15/0.70    inference(subsumption_resolution,[],[f70,f719])).
% 2.15/0.70  fof(f719,plain,(
% 2.15/0.70    ~v1_funct_1(sK4) | spl8_69),
% 2.15/0.70    inference(avatar_component_clause,[],[f718])).
% 2.15/0.70  fof(f725,plain,(
% 2.15/0.70    spl8_68),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f724])).
% 2.15/0.70  fof(f724,plain,(
% 2.15/0.70    $false | spl8_68),
% 2.15/0.70    inference(subsumption_resolution,[],[f193,f716])).
% 2.15/0.70  fof(f716,plain,(
% 2.15/0.70    ~v1_relat_1(sK4) | spl8_68),
% 2.15/0.70    inference(avatar_component_clause,[],[f715])).
% 2.15/0.70  fof(f193,plain,(
% 2.15/0.70    v1_relat_1(sK4)),
% 2.15/0.70    inference(resolution,[],[f71,f102])).
% 2.15/0.70  fof(f102,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f37])).
% 2.15/0.70  fof(f37,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.70    inference(ennf_transformation,[],[f11])).
% 2.15/0.70  fof(f11,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.15/0.70  fof(f601,plain,(
% 2.15/0.70    spl8_4 | ~spl8_9),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f599])).
% 2.15/0.70  fof(f599,plain,(
% 2.15/0.70    $false | (spl8_4 | ~spl8_9)),
% 2.15/0.70    inference(subsumption_resolution,[],[f153,f592])).
% 2.15/0.70  fof(f592,plain,(
% 2.15/0.70    v1_xboole_0(sK3) | ~spl8_9),
% 2.15/0.70    inference(resolution,[],[f175,f79])).
% 2.15/0.70  fof(f79,plain,(
% 2.15/0.70    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f55])).
% 2.15/0.70  fof(f55,plain,(
% 2.15/0.70    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.15/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).
% 2.15/0.70  fof(f54,plain,(
% 2.15/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f53,plain,(
% 2.15/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.15/0.70    inference(rectify,[],[f52])).
% 2.15/0.70  fof(f52,plain,(
% 2.15/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.15/0.70    inference(nnf_transformation,[],[f1])).
% 2.15/0.70  fof(f1,axiom,(
% 2.15/0.70    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.15/0.70  fof(f175,plain,(
% 2.15/0.70    ( ! [X3] : (~r2_hidden(X3,sK3)) ) | ~spl8_9),
% 2.15/0.70    inference(avatar_component_clause,[],[f174])).
% 2.15/0.70  fof(f153,plain,(
% 2.15/0.70    ~v1_xboole_0(sK3) | spl8_4),
% 2.15/0.70    inference(avatar_component_clause,[],[f152])).
% 2.15/0.70  fof(f591,plain,(
% 2.15/0.70    spl8_35),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f590])).
% 2.15/0.70  fof(f590,plain,(
% 2.15/0.70    $false | spl8_35),
% 2.15/0.70    inference(subsumption_resolution,[],[f67,f388])).
% 2.15/0.70  fof(f388,plain,(
% 2.15/0.70    ~v1_funct_1(sK3) | spl8_35),
% 2.15/0.70    inference(avatar_component_clause,[],[f387])).
% 2.15/0.70  fof(f274,plain,(
% 2.15/0.70    ~spl8_6),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f273])).
% 2.15/0.70  fof(f273,plain,(
% 2.15/0.70    $false | ~spl8_6),
% 2.15/0.70    inference(subsumption_resolution,[],[f76,f264])).
% 2.15/0.70  fof(f264,plain,(
% 2.15/0.70    ~v1_xboole_0(k1_xboole_0) | ~spl8_6),
% 2.15/0.70    inference(backward_demodulation,[],[f66,f161])).
% 2.15/0.70  fof(f161,plain,(
% 2.15/0.70    k1_xboole_0 = sK2 | ~spl8_6),
% 2.15/0.70    inference(avatar_component_clause,[],[f160])).
% 2.15/0.70  % SZS output end Proof for theBenchmark
% 2.15/0.70  % (14806)------------------------------
% 2.15/0.70  % (14806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.70  % (14806)Termination reason: Refutation
% 2.15/0.70  
% 2.15/0.70  % (14806)Memory used [KB]: 12281
% 2.15/0.70  % (14806)Time elapsed: 0.255 s
% 2.15/0.70  % (14806)------------------------------
% 2.15/0.70  % (14806)------------------------------
% 2.15/0.70  % (14799)Success in time 0.337 s
%------------------------------------------------------------------------------
