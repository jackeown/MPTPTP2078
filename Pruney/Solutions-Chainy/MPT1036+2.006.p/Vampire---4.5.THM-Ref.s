%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (13971 expanded)
%              Number of leaves         :   12 (4097 expanded)
%              Depth                    :   39
%              Number of atoms          :  549 (114533 expanded)
%              Number of equality atoms :  147 (23124 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(global_subsumption,[],[f240,f254,f260])).

fof(f260,plain,(
    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f259,f63])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f45,f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
        & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) )
      | ~ r1_partfun1(sK1,sK2) )
    & ( ! [X4] :
          ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
      | r1_partfun1(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                  & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
              | ~ r1_partfun1(X1,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
              | r1_partfun1(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
            | ~ r1_partfun1(sK1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(sK1,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
            | r1_partfun1(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
          | ~ r1_partfun1(sK1,X2) )
        & ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(sK1,X4)
              | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
          | r1_partfun1(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
            & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
        | ~ r1_partfun1(sK1,sK2) )
      & ( ! [X4] :
            ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
        | r1_partfun1(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
   => ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
      & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f259,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f258,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f258,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f255,f254])).

fof(f255,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f219,f172])).

fof(f172,plain,(
    r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f85,f162])).

fof(f162,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f161,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f150,f137])).

fof(f137,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f130,f68])).

fof(f68,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | r1_partfun1(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f38,f61])).

fof(f61,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f38,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f130,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f129,f63])).

fof(f129,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f125,f33])).

fof(f125,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f111,f85])).

fof(f111,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK4(X4,sK2),k1_relat_1(X4))
      | r1_partfun1(X4,sK2)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f110,f76])).

fof(f76,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f45,f37,f41])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK4(X4,sK2),k1_relat_1(X4))
      | r1_partfun1(X4,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f102,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK4(X4,sK2),k1_relat_1(X4))
      | r1_partfun1(X4,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f43,f94])).

fof(f94,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f82,f74])).

fof(f74,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f47])).

fof(f82,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
                & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(f150,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f147,f40])).

fof(f40,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f147,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f146,f69])).

fof(f69,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(backward_demodulation,[],[f39,f61])).

fof(f39,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f145,f68])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f144,f63])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_relat_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f141,f33])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f107,f85])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK2)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK2)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK2)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f42,f94])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f161,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f160,f150])).

fof(f160,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f159,f63])).

fof(f159,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f153,f33])).

fof(f153,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f115,f85])).

fof(f115,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2))
      | r1_partfun1(X6,sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f114,f76])).

fof(f114,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2))
      | r1_partfun1(X6,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f104,f35])).

fof(f104,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2))
      | r1_partfun1(X6,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f44,f94])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f60,f61])).

fof(f60,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f219,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2))
      | r1_partfun1(X7,sK2)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f218,f76])).

fof(f218,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2))
      | r1_partfun1(X7,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f207,f35])).

fof(f207,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2))
      | r1_partfun1(X7,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f44,f198])).

fof(f198,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f169,f186])).

fof(f186,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f164,f165,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f165,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f37,f162])).

fof(f164,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f162])).

fof(f169,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f74,f162])).

fof(f254,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f252,f40])).

fof(f252,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f246,f69])).

fof(f246,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f245,f68])).

fof(f245,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f244,f63])).

fof(f244,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f242,f33])).

fof(f242,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f211,f172])).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK2)
      | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f210,f76])).

fof(f210,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK2)
      | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f203,f35])).

fof(f203,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK2)
      | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f42,f198])).

fof(f240,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f235,f68])).

fof(f235,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f234,f63])).

fof(f234,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f232,f33])).

fof(f232,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f215,f172])).

fof(f215,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK4(X5,sK2),k1_relat_1(X5))
      | r1_partfun1(X5,sK2)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f214,f76])).

fof(f214,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK4(X5,sK2),k1_relat_1(X5))
      | r1_partfun1(X5,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f205,f35])).

fof(f205,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK4(X5,sK2),k1_relat_1(X5))
      | r1_partfun1(X5,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f43,f198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:08:48 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (7176)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (7179)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (7186)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (7184)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (7178)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (7187)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (7186)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f240,f254,f260])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f259,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f45,f34,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    (((k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) => (k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.21/0.52    inference(rectify,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f258,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f255,f254])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f219,f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f85,f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f161,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.21/0.52    inference(resolution,[],[f150,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f130,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK1)) | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | r1_partfun1(sK1,sK2)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f38,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f34,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) | r1_partfun1(sK1,sK2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f129,f63])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f33])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f111,f85])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK4(X4,sK2),k1_relat_1(X4)) | r1_partfun1(X4,sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f45,f37,f41])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK4(X4,sK2),k1_relat_1(X4)) | r1_partfun1(X4,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK4(X4,sK2),k1_relat_1(X4)) | r1_partfun1(X4,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(superposition,[],[f43,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f82,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f37,f47])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK0,sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ~v1_funct_2(sK2,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f37,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0 | ~r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f146,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    r2_hidden(sK3,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f61])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) | ~r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f68])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f144,f63])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f33])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(resolution,[],[f107,f85])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK2) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f76])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK2) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f35])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK2) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(superposition,[],[f42,f94])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f150])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f63])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f33])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f115,f85])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2)) | r1_partfun1(X6,sK2) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f76])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2)) | r1_partfun1(X6,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f35])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2)) | r1_partfun1(X6,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(superposition,[],[f44,f94])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f70,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f60,f61])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f34,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),k1_xboole_0) | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2)) | r1_partfun1(X7,sK2) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f218,f76])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),k1_xboole_0) | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2)) | r1_partfun1(X7,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f207,f35])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),k1_xboole_0) | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2)) | r1_partfun1(X7,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.21/0.52    inference(superposition,[],[f44,f198])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.52    inference(backward_demodulation,[],[f169,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f164,f165,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f37,f162])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f36,f162])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.52    inference(backward_demodulation,[],[f74,f162])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ~r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f252,f40])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f246,f69])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f245,f68])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f244,f63])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f242,f33])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(resolution,[],[f211,f172])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r1_partfun1(X2,sK2) | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f210,f76])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r1_partfun1(X2,sK2) | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3) | ~v1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f203,f35])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r1_partfun1(X2,sK2) | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(superposition,[],[f42,f198])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f239])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f235,f68])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f63])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f33])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f215,f172])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k1_xboole_0) | r2_hidden(sK4(X5,sK2),k1_relat_1(X5)) | r1_partfun1(X5,sK2) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f214,f76])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k1_xboole_0) | r2_hidden(sK4(X5,sK2),k1_relat_1(X5)) | r1_partfun1(X5,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f205,f35])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k1_xboole_0) | r2_hidden(sK4(X5,sK2),k1_relat_1(X5)) | r1_partfun1(X5,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.21/0.52    inference(superposition,[],[f43,f198])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7186)------------------------------
% 0.21/0.52  % (7186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7186)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7186)Memory used [KB]: 6268
% 0.21/0.52  % (7186)Time elapsed: 0.098 s
% 0.21/0.52  % (7186)------------------------------
% 0.21/0.52  % (7186)------------------------------
% 0.21/0.52  % (7170)Success in time 0.16 s
%------------------------------------------------------------------------------
