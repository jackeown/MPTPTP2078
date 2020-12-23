%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:12 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 831 expanded)
%              Number of leaves         :   27 ( 214 expanded)
%              Depth                    :   17
%              Number of atoms          :  522 (4943 expanded)
%              Number of equality atoms :  107 (1074 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f121,f169,f272,f556,f557,f558,f634,f679,f1340,f1357])).

fof(f1357,plain,
    ( spl4_3
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1346,f206])).

fof(f206,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f204,f192])).

fof(f192,plain,(
    ! [X1] : v1_relat_1(k7_relat_1(sK3,X1)) ),
    inference(resolution,[],[f189,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f189,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f188,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f188,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f187,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f187,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f90,f150])).

fof(f150,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f137,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f204,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f194,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f194,plain,(
    ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1) ),
    inference(resolution,[],[f189,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1346,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f1031,f1341])).

fof(f1341,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f111,f150])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1031,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1030,f192])).

fof(f1030,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1026,f185])).

fof(f185,plain,(
    ! [X1] : v1_funct_1(k7_relat_1(sK3,X1)) ),
    inference(backward_demodulation,[],[f151,f150])).

fof(f151,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ),
    inference(subsumption_resolution,[],[f138,f53])).

fof(f138,plain,(
    ! [X1] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1026,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(superposition,[],[f72,f474])).

fof(f474,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_15 ),
    inference(resolution,[],[f308,f56])).

fof(f56,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f308,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f301,f133])).

fof(f133,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f79])).

fof(f301,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl4_15 ),
    inference(superposition,[],[f67,f298])).

fof(f298,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f134,f249])).

fof(f249,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl4_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f134,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1340,plain,
    ( spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f1339])).

fof(f1339,plain,
    ( $false
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1338,f186])).

fof(f186,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f107,f150])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1338,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_15 ),
    inference(resolution,[],[f1029,f206])).

fof(f1029,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1028,f192])).

fof(f1028,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1025,f185])).

fof(f1025,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_15 ),
    inference(superposition,[],[f71,f474])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f679,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f675,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f675,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f639,f674])).

fof(f674,plain,
    ( ! [X0] : k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f673,f622])).

fof(f622,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(resolution,[],[f611,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f611,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0))
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f328,f559])).

fof(f559,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_9 ),
    inference(resolution,[],[f146,f62])).

fof(f146,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f328,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_16
  <=> ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f673,plain,
    ( ! [X0] : k7_relat_1(k1_xboole_0,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f672,f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f672,plain,
    ( ! [X0] : k7_relat_1(k1_xboole_0,X0) = k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f564,f559])).

fof(f564,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,k1_xboole_0,sK3,X0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f150,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f639,plain,
    ( ~ m1_subset_1(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f638,f120])).

fof(f638,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f637,f559])).

fof(f637,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f636,f581])).

fof(f581,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f580,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f580,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f266,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f266,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f56,f120])).

fof(f636,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f635,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f635,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f111,f115])).

fof(f634,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f631,f597])).

fof(f597,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f583,f559])).

fof(f583,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f561,f120])).

fof(f561,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f54,f115])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f631,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f602,f622])).

fof(f602,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f601,f559])).

fof(f601,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f257,f581])).

fof(f257,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f186,f115])).

fof(f558,plain,
    ( spl4_15
    | spl4_4 ),
    inference(avatar_split_clause,[],[f287,f114,f247])).

fof(f287,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f284,f54])).

fof(f284,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f55,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f557,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f386,f144,f140])).

fof(f140,plain,
    ( spl4_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f386,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f556,plain,
    ( ~ spl4_8
    | spl4_16 ),
    inference(avatar_split_clause,[],[f432,f327,f140])).

fof(f432,plain,(
    ! [X0] :
      ( v1_xboole_0(k7_relat_1(sK3,X0))
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f189,f65])).

fof(f272,plain,
    ( ~ spl4_5
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl4_5
    | spl4_8 ),
    inference(subsumption_resolution,[],[f268,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f268,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | spl4_8 ),
    inference(backward_demodulation,[],[f142,f120])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f169,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f151,f103])).

fof(f103,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f121,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f57,f118,f114])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f109,f105,f101])).

fof(f58,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (18301)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (18309)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (18292)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (18299)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (18291)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (18295)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (18296)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (18289)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (18293)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (18310)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.56  % (18302)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.56  % (18306)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (18290)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (18313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.57  % (18300)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.57  % (18298)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.57  % (18294)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.57  % (18288)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.57  % (18305)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.58  % (18312)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.58  % (18307)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.58  % (18297)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.58  % (18304)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.58  % (18303)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.59  % (18311)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.59  % (18308)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.99/0.62  % (18289)Refutation found. Thanks to Tanya!
% 1.99/0.62  % SZS status Theorem for theBenchmark
% 1.99/0.62  % SZS output start Proof for theBenchmark
% 1.99/0.62  fof(f1393,plain,(
% 1.99/0.62    $false),
% 1.99/0.62    inference(avatar_sat_refutation,[],[f112,f121,f169,f272,f556,f557,f558,f634,f679,f1340,f1357])).
% 1.99/0.62  fof(f1357,plain,(
% 1.99/0.62    spl4_3 | ~spl4_15),
% 1.99/0.62    inference(avatar_contradiction_clause,[],[f1356])).
% 1.99/0.62  fof(f1356,plain,(
% 1.99/0.62    $false | (spl4_3 | ~spl4_15)),
% 1.99/0.62    inference(subsumption_resolution,[],[f1346,f206])).
% 1.99/0.62  fof(f206,plain,(
% 1.99/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.99/0.62    inference(subsumption_resolution,[],[f204,f192])).
% 1.99/0.62  fof(f192,plain,(
% 1.99/0.62    ( ! [X1] : (v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.99/0.62    inference(resolution,[],[f189,f79])).
% 1.99/0.62  fof(f79,plain,(
% 1.99/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f36])).
% 1.99/0.62  fof(f36,plain,(
% 1.99/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.62    inference(ennf_transformation,[],[f13])).
% 1.99/0.62  fof(f13,axiom,(
% 1.99/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.99/0.62  fof(f189,plain,(
% 1.99/0.62    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.99/0.62    inference(subsumption_resolution,[],[f188,f53])).
% 1.99/0.62  fof(f53,plain,(
% 1.99/0.62    v1_funct_1(sK3)),
% 1.99/0.62    inference(cnf_transformation,[],[f46])).
% 1.99/0.62  fof(f46,plain,(
% 1.99/0.62    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.99/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f45])).
% 1.99/0.62  fof(f45,plain,(
% 1.99/0.62    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.99/0.62    introduced(choice_axiom,[])).
% 1.99/0.62  fof(f26,plain,(
% 1.99/0.62    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.99/0.62    inference(flattening,[],[f25])).
% 1.99/0.62  fof(f25,plain,(
% 1.99/0.62    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.99/0.62    inference(ennf_transformation,[],[f22])).
% 1.99/0.62  fof(f22,negated_conjecture,(
% 1.99/0.62    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.99/0.62    inference(negated_conjecture,[],[f21])).
% 1.99/0.62  fof(f21,conjecture,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.99/0.62  fof(f188,plain,(
% 1.99/0.62    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.99/0.62    inference(subsumption_resolution,[],[f187,f55])).
% 1.99/0.62  fof(f55,plain,(
% 1.99/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.99/0.62    inference(cnf_transformation,[],[f46])).
% 1.99/0.62  fof(f187,plain,(
% 1.99/0.62    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.99/0.62    inference(superposition,[],[f90,f150])).
% 1.99/0.62  fof(f150,plain,(
% 1.99/0.62    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.99/0.62    inference(subsumption_resolution,[],[f137,f53])).
% 1.99/0.62  fof(f137,plain,(
% 1.99/0.62    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.99/0.62    inference(resolution,[],[f55,f88])).
% 1.99/0.62  fof(f88,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f42])).
% 1.99/0.62  fof(f42,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.99/0.62    inference(flattening,[],[f41])).
% 1.99/0.62  fof(f41,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.99/0.62    inference(ennf_transformation,[],[f19])).
% 1.99/0.62  fof(f19,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.99/0.62  fof(f90,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f44])).
% 1.99/0.62  fof(f44,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.99/0.62    inference(flattening,[],[f43])).
% 1.99/0.62  fof(f43,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.99/0.62    inference(ennf_transformation,[],[f18])).
% 1.99/0.62  fof(f18,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.99/0.62  fof(f204,plain,(
% 1.99/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.99/0.62    inference(resolution,[],[f194,f68])).
% 1.99/0.63  fof(f68,plain,(
% 1.99/0.63    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f47])).
% 1.99/0.63  fof(f47,plain,(
% 1.99/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.99/0.63    inference(nnf_transformation,[],[f33])).
% 1.99/0.63  fof(f33,plain,(
% 1.99/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/0.63    inference(ennf_transformation,[],[f8])).
% 1.99/0.63  fof(f8,axiom,(
% 1.99/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.99/0.63  fof(f194,plain,(
% 1.99/0.63    ( ! [X3] : (v5_relat_1(k7_relat_1(sK3,X3),sK1)) )),
% 1.99/0.63    inference(resolution,[],[f189,f81])).
% 1.99/0.63  fof(f81,plain,(
% 1.99/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f38])).
% 1.99/0.63  fof(f38,plain,(
% 1.99/0.63    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.63    inference(ennf_transformation,[],[f23])).
% 1.99/0.63  fof(f23,plain,(
% 1.99/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.99/0.63    inference(pure_predicate_removal,[],[f14])).
% 1.99/0.63  fof(f14,axiom,(
% 1.99/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.99/0.63  fof(f1346,plain,(
% 1.99/0.63    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_15)),
% 1.99/0.63    inference(resolution,[],[f1031,f1341])).
% 1.99/0.63  fof(f1341,plain,(
% 1.99/0.63    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.99/0.63    inference(forward_demodulation,[],[f111,f150])).
% 1.99/0.63  fof(f111,plain,(
% 1.99/0.63    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.99/0.63    inference(avatar_component_clause,[],[f109])).
% 1.99/0.63  fof(f109,plain,(
% 1.99/0.63    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.99/0.63  fof(f1031,plain,(
% 1.99/0.63    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl4_15),
% 1.99/0.63    inference(subsumption_resolution,[],[f1030,f192])).
% 1.99/0.63  fof(f1030,plain,(
% 1.99/0.63    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 1.99/0.63    inference(subsumption_resolution,[],[f1026,f185])).
% 1.99/0.63  fof(f185,plain,(
% 1.99/0.63    ( ! [X1] : (v1_funct_1(k7_relat_1(sK3,X1))) )),
% 1.99/0.63    inference(backward_demodulation,[],[f151,f150])).
% 1.99/0.63  fof(f151,plain,(
% 1.99/0.63    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 1.99/0.63    inference(subsumption_resolution,[],[f138,f53])).
% 1.99/0.63  fof(f138,plain,(
% 1.99/0.63    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) | ~v1_funct_1(sK3)) )),
% 1.99/0.63    inference(resolution,[],[f55,f89])).
% 1.99/0.63  fof(f89,plain,(
% 1.99/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f44])).
% 1.99/0.63  fof(f1026,plain,(
% 1.99/0.63    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 1.99/0.63    inference(superposition,[],[f72,f474])).
% 1.99/0.63  fof(f474,plain,(
% 1.99/0.63    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_15),
% 1.99/0.63    inference(resolution,[],[f308,f56])).
% 1.99/0.63  fof(f56,plain,(
% 1.99/0.63    r1_tarski(sK2,sK0)),
% 1.99/0.63    inference(cnf_transformation,[],[f46])).
% 1.99/0.63  fof(f308,plain,(
% 1.99/0.63    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl4_15),
% 1.99/0.63    inference(subsumption_resolution,[],[f301,f133])).
% 1.99/0.63  fof(f133,plain,(
% 1.99/0.63    v1_relat_1(sK3)),
% 1.99/0.63    inference(resolution,[],[f55,f79])).
% 1.99/0.63  fof(f301,plain,(
% 1.99/0.63    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl4_15),
% 1.99/0.63    inference(superposition,[],[f67,f298])).
% 1.99/0.63  fof(f298,plain,(
% 1.99/0.63    sK0 = k1_relat_1(sK3) | ~spl4_15),
% 1.99/0.63    inference(forward_demodulation,[],[f134,f249])).
% 1.99/0.63  fof(f249,plain,(
% 1.99/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_15),
% 1.99/0.63    inference(avatar_component_clause,[],[f247])).
% 1.99/0.63  fof(f247,plain,(
% 1.99/0.63    spl4_15 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.99/0.63  fof(f134,plain,(
% 1.99/0.63    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.99/0.63    inference(resolution,[],[f55,f80])).
% 1.99/0.63  fof(f80,plain,(
% 1.99/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f37])).
% 1.99/0.63  fof(f37,plain,(
% 1.99/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.63    inference(ennf_transformation,[],[f16])).
% 1.99/0.63  fof(f16,axiom,(
% 1.99/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.99/0.63  fof(f67,plain,(
% 1.99/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f32])).
% 1.99/0.63  fof(f32,plain,(
% 1.99/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.99/0.63    inference(flattening,[],[f31])).
% 1.99/0.65  fof(f31,plain,(
% 1.99/0.65    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.99/0.65    inference(ennf_transformation,[],[f11])).
% 1.99/0.65  fof(f11,axiom,(
% 1.99/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.99/0.65  fof(f72,plain,(
% 1.99/0.65    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f35])).
% 1.99/0.65  fof(f35,plain,(
% 1.99/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.99/0.65    inference(flattening,[],[f34])).
% 1.99/0.65  fof(f34,plain,(
% 1.99/0.65    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.99/0.65    inference(ennf_transformation,[],[f20])).
% 1.99/0.65  fof(f20,axiom,(
% 1.99/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.99/0.65  fof(f1340,plain,(
% 1.99/0.65    spl4_2 | ~spl4_15),
% 1.99/0.65    inference(avatar_contradiction_clause,[],[f1339])).
% 1.99/0.65  fof(f1339,plain,(
% 1.99/0.65    $false | (spl4_2 | ~spl4_15)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1338,f186])).
% 1.99/0.65  fof(f186,plain,(
% 1.99/0.65    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.99/0.65    inference(backward_demodulation,[],[f107,f150])).
% 1.99/0.65  fof(f107,plain,(
% 1.99/0.65    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.99/0.65    inference(avatar_component_clause,[],[f105])).
% 1.99/0.65  fof(f105,plain,(
% 1.99/0.65    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.99/0.65  fof(f1338,plain,(
% 1.99/0.65    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_15),
% 1.99/0.65    inference(resolution,[],[f1029,f206])).
% 1.99/0.65  fof(f1029,plain,(
% 1.99/0.65    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | ~spl4_15),
% 1.99/0.65    inference(subsumption_resolution,[],[f1028,f192])).
% 1.99/0.65  fof(f1028,plain,(
% 1.99/0.65    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 1.99/0.65    inference(subsumption_resolution,[],[f1025,f185])).
% 1.99/0.65  fof(f1025,plain,(
% 1.99/0.65    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_15),
% 1.99/0.65    inference(superposition,[],[f71,f474])).
% 1.99/0.65  fof(f71,plain,(
% 1.99/0.65    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f35])).
% 1.99/0.65  fof(f679,plain,(
% 1.99/0.65    spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16),
% 1.99/0.65    inference(avatar_contradiction_clause,[],[f678])).
% 1.99/0.65  fof(f678,plain,(
% 1.99/0.65    $false | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(subsumption_resolution,[],[f675,f61])).
% 1.99/0.65  fof(f61,plain,(
% 1.99/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.99/0.65    inference(cnf_transformation,[],[f6])).
% 1.99/0.65  fof(f6,axiom,(
% 1.99/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.99/0.65  fof(f675,plain,(
% 1.99/0.65    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(backward_demodulation,[],[f639,f674])).
% 1.99/0.65  fof(f674,plain,(
% 1.99/0.65    ( ! [X0] : (k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(forward_demodulation,[],[f673,f622])).
% 1.99/0.65  fof(f622,plain,(
% 1.99/0.65    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(resolution,[],[f611,f62])).
% 1.99/0.65  fof(f62,plain,(
% 1.99/0.65    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.99/0.65    inference(cnf_transformation,[],[f27])).
% 1.99/0.65  fof(f27,plain,(
% 1.99/0.65    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.99/0.65    inference(ennf_transformation,[],[f2])).
% 1.99/0.65  fof(f2,axiom,(
% 1.99/0.65    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.99/0.65  fof(f611,plain,(
% 1.99/0.65    ( ! [X0] : (v1_xboole_0(k7_relat_1(k1_xboole_0,X0))) ) | (~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(forward_demodulation,[],[f328,f559])).
% 1.99/0.65  fof(f559,plain,(
% 1.99/0.65    k1_xboole_0 = sK3 | ~spl4_9),
% 1.99/0.65    inference(resolution,[],[f146,f62])).
% 1.99/0.65  fof(f146,plain,(
% 1.99/0.65    v1_xboole_0(sK3) | ~spl4_9),
% 1.99/0.65    inference(avatar_component_clause,[],[f144])).
% 1.99/0.65  fof(f144,plain,(
% 1.99/0.65    spl4_9 <=> v1_xboole_0(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.99/0.65  fof(f328,plain,(
% 1.99/0.65    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK3,X0))) ) | ~spl4_16),
% 1.99/0.65    inference(avatar_component_clause,[],[f327])).
% 1.99/0.65  fof(f327,plain,(
% 1.99/0.65    spl4_16 <=> ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.99/0.65  fof(f673,plain,(
% 1.99/0.65    ( ! [X0] : (k7_relat_1(k1_xboole_0,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.99/0.65    inference(forward_demodulation,[],[f672,f120])).
% 1.99/0.65  fof(f120,plain,(
% 1.99/0.65    k1_xboole_0 = sK0 | ~spl4_5),
% 1.99/0.65    inference(avatar_component_clause,[],[f118])).
% 1.99/0.65  fof(f118,plain,(
% 1.99/0.65    spl4_5 <=> k1_xboole_0 = sK0),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.99/0.65  fof(f672,plain,(
% 1.99/0.65    ( ! [X0] : (k7_relat_1(k1_xboole_0,X0) = k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_9)),
% 1.99/0.65    inference(forward_demodulation,[],[f564,f559])).
% 1.99/0.65  fof(f564,plain,(
% 1.99/0.65    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,k1_xboole_0,sK3,X0)) ) | ~spl4_4),
% 1.99/0.65    inference(backward_demodulation,[],[f150,f115])).
% 1.99/0.65  fof(f115,plain,(
% 1.99/0.65    k1_xboole_0 = sK1 | ~spl4_4),
% 1.99/0.65    inference(avatar_component_clause,[],[f114])).
% 1.99/0.65  fof(f114,plain,(
% 1.99/0.65    spl4_4 <=> k1_xboole_0 = sK1),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.99/0.65  fof(f639,plain,(
% 1.99/0.65    ~m1_subset_1(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.99/0.65    inference(forward_demodulation,[],[f638,f120])).
% 1.99/0.65  fof(f638,plain,(
% 1.99/0.65    ~m1_subset_1(k2_partfun1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.99/0.65    inference(forward_demodulation,[],[f637,f559])).
% 1.99/0.65  fof(f637,plain,(
% 1.99/0.65    ~m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.99/0.65    inference(forward_demodulation,[],[f636,f581])).
% 1.99/0.65  fof(f581,plain,(
% 1.99/0.65    k1_xboole_0 = sK2 | ~spl4_5),
% 1.99/0.65    inference(subsumption_resolution,[],[f580,f60])).
% 1.99/0.65  fof(f60,plain,(
% 1.99/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f4])).
% 1.99/0.65  fof(f4,axiom,(
% 1.99/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.99/0.65  fof(f580,plain,(
% 1.99/0.65    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl4_5),
% 1.99/0.65    inference(resolution,[],[f266,f75])).
% 1.99/0.65  fof(f75,plain,(
% 1.99/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f49])).
% 1.99/0.65  fof(f49,plain,(
% 1.99/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.65    inference(flattening,[],[f48])).
% 1.99/0.65  fof(f48,plain,(
% 1.99/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.65    inference(nnf_transformation,[],[f3])).
% 1.99/0.65  fof(f3,axiom,(
% 1.99/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.99/0.65  fof(f266,plain,(
% 1.99/0.65    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.99/0.65    inference(backward_demodulation,[],[f56,f120])).
% 1.99/0.65  fof(f636,plain,(
% 1.99/0.65    ~m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 1.99/0.65    inference(forward_demodulation,[],[f635,f93])).
% 1.99/0.65  fof(f93,plain,(
% 1.99/0.65    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.99/0.65    inference(equality_resolution,[],[f78])).
% 1.99/0.65  fof(f78,plain,(
% 1.99/0.65    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.99/0.65    inference(cnf_transformation,[],[f51])).
% 1.99/0.65  fof(f51,plain,(
% 1.99/0.65    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.99/0.65    inference(flattening,[],[f50])).
% 1.99/0.65  fof(f50,plain,(
% 1.99/0.65    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.99/0.65    inference(nnf_transformation,[],[f5])).
% 1.99/0.65  fof(f5,axiom,(
% 1.99/0.65    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.99/0.65  fof(f635,plain,(
% 1.99/0.65    ~m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl4_3 | ~spl4_4)),
% 1.99/0.65    inference(forward_demodulation,[],[f111,f115])).
% 1.99/0.65  fof(f634,plain,(
% 1.99/0.65    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16),
% 1.99/0.65    inference(avatar_contradiction_clause,[],[f633])).
% 1.99/0.65  fof(f633,plain,(
% 1.99/0.65    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(subsumption_resolution,[],[f631,f597])).
% 1.99/0.65  fof(f597,plain,(
% 1.99/0.65    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.99/0.65    inference(forward_demodulation,[],[f583,f559])).
% 1.99/0.65  fof(f583,plain,(
% 1.99/0.65    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.99/0.65    inference(forward_demodulation,[],[f561,f120])).
% 1.99/0.65  fof(f561,plain,(
% 1.99/0.65    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.99/0.65    inference(backward_demodulation,[],[f54,f115])).
% 1.99/0.65  fof(f54,plain,(
% 1.99/0.65    v1_funct_2(sK3,sK0,sK1)),
% 1.99/0.65    inference(cnf_transformation,[],[f46])).
% 1.99/0.65  fof(f631,plain,(
% 1.99/0.65    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_16)),
% 1.99/0.65    inference(backward_demodulation,[],[f602,f622])).
% 1.99/0.65  fof(f602,plain,(
% 1.99/0.65    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.99/0.65    inference(forward_demodulation,[],[f601,f559])).
% 1.99/0.65  fof(f601,plain,(
% 1.99/0.65    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.99/0.65    inference(forward_demodulation,[],[f257,f581])).
% 1.99/0.65  fof(f257,plain,(
% 1.99/0.65    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.99/0.65    inference(backward_demodulation,[],[f186,f115])).
% 1.99/0.65  fof(f558,plain,(
% 1.99/0.65    spl4_15 | spl4_4),
% 1.99/0.65    inference(avatar_split_clause,[],[f287,f114,f247])).
% 1.99/0.65  fof(f287,plain,(
% 1.99/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.99/0.65    inference(subsumption_resolution,[],[f284,f54])).
% 1.99/0.65  fof(f284,plain,(
% 1.99/0.65    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.99/0.65    inference(resolution,[],[f55,f82])).
% 1.99/0.65  fof(f82,plain,(
% 1.99/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.99/0.65    inference(cnf_transformation,[],[f52])).
% 1.99/0.65  fof(f52,plain,(
% 1.99/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.65    inference(nnf_transformation,[],[f40])).
% 1.99/0.65  fof(f40,plain,(
% 1.99/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.65    inference(flattening,[],[f39])).
% 1.99/0.65  fof(f39,plain,(
% 1.99/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.65    inference(ennf_transformation,[],[f17])).
% 1.99/0.65  fof(f17,axiom,(
% 1.99/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.99/0.65  fof(f557,plain,(
% 1.99/0.65    ~spl4_8 | spl4_9),
% 1.99/0.65    inference(avatar_split_clause,[],[f386,f144,f140])).
% 1.99/0.65  fof(f140,plain,(
% 1.99/0.65    spl4_8 <=> v1_xboole_0(sK0)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.99/0.65  fof(f386,plain,(
% 1.99/0.65    v1_xboole_0(sK3) | ~v1_xboole_0(sK0)),
% 1.99/0.65    inference(resolution,[],[f55,f65])).
% 1.99/0.65  fof(f65,plain,(
% 1.99/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f29])).
% 1.99/0.65  fof(f29,plain,(
% 1.99/0.65    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.99/0.65    inference(ennf_transformation,[],[f15])).
% 1.99/0.65  fof(f15,axiom,(
% 1.99/0.65    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.99/0.65  fof(f556,plain,(
% 1.99/0.65    ~spl4_8 | spl4_16),
% 1.99/0.65    inference(avatar_split_clause,[],[f432,f327,f140])).
% 1.99/0.65  fof(f432,plain,(
% 1.99/0.65    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK3,X0)) | ~v1_xboole_0(sK0)) )),
% 1.99/0.65    inference(resolution,[],[f189,f65])).
% 1.99/0.65  fof(f272,plain,(
% 1.99/0.65    ~spl4_5 | spl4_8),
% 1.99/0.65    inference(avatar_contradiction_clause,[],[f271])).
% 1.99/0.65  fof(f271,plain,(
% 1.99/0.65    $false | (~spl4_5 | spl4_8)),
% 1.99/0.65    inference(subsumption_resolution,[],[f268,f59])).
% 1.99/0.65  fof(f59,plain,(
% 1.99/0.65    v1_xboole_0(k1_xboole_0)),
% 1.99/0.65    inference(cnf_transformation,[],[f1])).
% 1.99/0.65  fof(f1,axiom,(
% 1.99/0.65    v1_xboole_0(k1_xboole_0)),
% 1.99/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.99/0.65  fof(f268,plain,(
% 1.99/0.65    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | spl4_8)),
% 1.99/0.65    inference(backward_demodulation,[],[f142,f120])).
% 1.99/0.65  fof(f142,plain,(
% 1.99/0.65    ~v1_xboole_0(sK0) | spl4_8),
% 1.99/0.65    inference(avatar_component_clause,[],[f140])).
% 1.99/0.65  fof(f169,plain,(
% 1.99/0.65    spl4_1),
% 1.99/0.65    inference(avatar_contradiction_clause,[],[f168])).
% 1.99/0.65  fof(f168,plain,(
% 1.99/0.65    $false | spl4_1),
% 1.99/0.65    inference(resolution,[],[f151,f103])).
% 1.99/0.65  fof(f103,plain,(
% 1.99/0.65    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.99/0.65    inference(avatar_component_clause,[],[f101])).
% 1.99/0.65  fof(f101,plain,(
% 1.99/0.65    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.99/0.65  fof(f121,plain,(
% 1.99/0.65    ~spl4_4 | spl4_5),
% 1.99/0.65    inference(avatar_split_clause,[],[f57,f118,f114])).
% 1.99/0.65  fof(f57,plain,(
% 1.99/0.65    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.99/0.65    inference(cnf_transformation,[],[f46])).
% 1.99/0.65  fof(f112,plain,(
% 1.99/0.65    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.99/0.65    inference(avatar_split_clause,[],[f58,f109,f105,f101])).
% 1.99/0.65  fof(f58,plain,(
% 1.99/0.65    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.99/0.65    inference(cnf_transformation,[],[f46])).
% 1.99/0.65  % SZS output end Proof for theBenchmark
% 1.99/0.65  % (18289)------------------------------
% 1.99/0.65  % (18289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.65  % (18289)Termination reason: Refutation
% 1.99/0.65  
% 1.99/0.65  % (18289)Memory used [KB]: 11129
% 1.99/0.65  % (18289)Time elapsed: 0.218 s
% 1.99/0.65  % (18289)------------------------------
% 1.99/0.65  % (18289)------------------------------
% 2.20/0.65  % (18287)Success in time 0.287 s
%------------------------------------------------------------------------------
