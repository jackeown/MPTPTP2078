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
% DateTime   : Thu Dec  3 13:06:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 (29537 expanded)
%              Number of leaves         :   11 (8535 expanded)
%              Depth                    :   36
%              Number of atoms          :  546 (289308 expanded)
%              Number of equality atoms :  162 (91335 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(global_subsumption,[],[f263,f276,f285])).

fof(f285,plain,(
    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f276,f277,f69])).

fof(f69,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(sK2))
      | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | r1_partfun1(sK2,sK3) ) ),
    inference(backward_demodulation,[],[f39,f62])).

fof(f62,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
        & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) )
      | ~ r1_partfun1(sK2,sK3) )
    & ( ! [X5] :
          ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
      | r1_partfun1(sK2,sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
                & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
            | ~ r1_partfun1(sK2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
            | r1_partfun1(sK2,X3) )
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
              & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
          | ~ r1_partfun1(sK2,X3) )
        & ( ! [X5] :
              ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
              | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
          | r1_partfun1(sK2,X3) )
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ( ? [X4] :
            ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
            & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
        | ~ r1_partfun1(sK2,sK3) )
      & ( ! [X5] :
            ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
        | r1_partfun1(sK2,sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X4] :
        ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
        & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
   => ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(f39,plain,(
    ! [X5] :
      ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f277,plain,(
    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f63,f33,f276,f191,f250])).

fof(f250,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
      | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
      | r1_partfun1(X4,sK3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f249,f75])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f249,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
      | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
      | r1_partfun1(X4,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f239,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f239,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
      | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
      | r1_partfun1(X4,sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f43,f230])).

fof(f230,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f197,f219])).

fof(f219,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(unit_resulting_resolution,[],[f194,f195,f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f195,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f183,f186])).

fof(f186,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f180,f38])).

fof(f38,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f180,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f162,f174,f179])).

fof(f179,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f178,f174])).

fof(f178,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f177,f75])).

fof(f177,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f176,f35])).

fof(f176,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f175,f61])).

fof(f61,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f175,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f100,f104])).

fof(f104,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f81,f74])).

fof(f74,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f37,f48])).

fof(f81,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    ! [X3] :
      ( ~ v4_relat_1(sK2,k1_relat_1(X3))
      | k1_funct_1(sK2,sK5(sK2,X3)) != k1_funct_1(X3,sK5(sK2,X3))
      | r1_partfun1(sK2,X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f99,f63])).

fof(f99,plain,(
    ! [X3] :
      ( ~ v4_relat_1(sK2,k1_relat_1(X3))
      | k1_funct_1(sK2,sK5(sK2,X3)) != k1_funct_1(X3,sK5(sK2,X3))
      | r1_partfun1(sK2,X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f94,f33])).

fof(f94,plain,(
    ! [X3] :
      ( ~ v4_relat_1(sK2,k1_relat_1(X3))
      | k1_funct_1(sK2,sK5(sK2,X3)) != k1_funct_1(X3,sK5(sK2,X3))
      | r1_partfun1(sK2,X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f82,f44])).

% (24634)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f82,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f170,f41])).

fof(f41,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f170,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f167,f70])).

fof(f70,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(backward_demodulation,[],[f40,f62])).

fof(f40,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f166,f69])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f165,f75])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f164,f35])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f163,f61])).

fof(f163,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f96,f104])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK2,k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,X0)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f95,f63])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK2,k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,X0)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f33])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK2,k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,X0)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f162,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f155,f69])).

fof(f155,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f154,f63])).

fof(f154,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f148,f33])).

fof(f148,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f133,f86])).

fof(f86,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f63,f61,f45])).

fof(f133,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | r2_hidden(sK5(X6,sK3),k1_relat_1(X6))
      | r1_partfun1(X6,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f132,f75])).

fof(f132,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | r2_hidden(sK5(X6,sK3),k1_relat_1(X6))
      | r1_partfun1(X6,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f124,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | r2_hidden(sK5(X6,sK3),k1_relat_1(X6))
      | r1_partfun1(X6,sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f43,f104])).

fof(f183,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f37,f180])).

fof(f194,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f182,f186])).

fof(f182,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f180])).

fof(f197,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f185,f186])).

fof(f185,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f74,f180])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f191,plain,(
    r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f86,f186])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f34,f47])).

fof(f276,plain,(
    ~ r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f274,f41])).

fof(f274,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f260,f70])).

fof(f260,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_relat_1(sK2))
      | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8) ) ),
    inference(subsumption_resolution,[],[f259,f69])).

fof(f259,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8) ) ),
    inference(subsumption_resolution,[],[f258,f75])).

fof(f258,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f257,f35])).

fof(f257,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f243,f189])).

fof(f189,plain,(
    v4_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f61,f186])).

fof(f243,plain,(
    ! [X8] :
      ( ~ v4_relat_1(sK2,k1_xboole_0)
      | ~ r2_hidden(X8,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f96,f230])).

fof(f263,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f262,f75])).

fof(f262,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f261,f35])).

fof(f261,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f244,f189])).

fof(f244,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f100,f230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (24641)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (24633)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (24637)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (24646)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (24638)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (24631)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (24639)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (24650)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (24646)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(global_subsumption,[],[f263,f276,f285])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f276,f277,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK2)) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f39,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f34,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) => (k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.50    inference(rectify,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f63,f33,f276,f191,f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f37,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f239,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(superposition,[],[f43,f230])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f197,f219])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f194,f195,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f183,f186])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    k1_xboole_0 = sK0),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f180,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    k1_xboole_0 = sK1),
% 0.21/0.50    inference(global_subsumption,[],[f162,f174,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f178,f174])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f177,f75])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f176,f35])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f175,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v4_relat_1(sK2,sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f34,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ~v4_relat_1(sK2,sK0) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f100,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(superposition,[],[f81,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f37,f48])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(resolution,[],[f37,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X3] : (~v4_relat_1(sK2,k1_relat_1(X3)) | k1_funct_1(sK2,sK5(sK2,X3)) != k1_funct_1(X3,sK5(sK2,X3)) | r1_partfun1(sK2,X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f99,f63])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X3] : (~v4_relat_1(sK2,k1_relat_1(X3)) | k1_funct_1(sK2,sK5(sK2,X3)) != k1_funct_1(X3,sK5(sK2,X3)) | r1_partfun1(sK2,X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f94,f33])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X3] : (~v4_relat_1(sK2,k1_relat_1(X3)) | k1_funct_1(sK2,sK5(sK2,X3)) != k1_funct_1(X3,sK5(sK2,X3)) | r1_partfun1(sK2,X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f82,f44])).
% 0.21/0.50  % (24634)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v4_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f63,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1 | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(resolution,[],[f167,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f40,f62])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f166,f69])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f165,f75])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f35])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f61])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK2,sK0) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(superposition,[],[f96,f104])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_relat_1(sK2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~r1_partfun1(sK2,X0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f63])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_relat_1(sK2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~r1_partfun1(sK2,X0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f33])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_relat_1(sK2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~r1_partfun1(sK2,X0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f82,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    r1_partfun1(sK2,sK3) | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    r1_partfun1(sK2,sK3) | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(resolution,[],[f155,f69])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f154,f63])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | ~v1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f33])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(resolution,[],[f133,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f63,f61,f45])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | r2_hidden(sK5(X6,sK3),k1_relat_1(X6)) | r1_partfun1(X6,sK3) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f75])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | r2_hidden(sK5(X6,sK3),k1_relat_1(X6)) | r1_partfun1(X6,sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f35])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | r2_hidden(sK5(X6,sK3),k1_relat_1(X6)) | r1_partfun1(X6,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK1) )),
% 0.21/0.50    inference(superposition,[],[f43,f104])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f37,f180])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f182,f186])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f36,f180])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f185,f186])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f74,f180])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f86,f186])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f34,f47])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f274,f41])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(resolution,[],[f260,f70])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(sK2)) | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f69])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f258,f75])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8) | ~v1_relat_1(sK3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f257,f35])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f243,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    v4_relat_1(sK2,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f61,f186])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X8] : (~v4_relat_1(sK2,k1_xboole_0) | ~r2_hidden(X8,k1_relat_1(sK2)) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK3,X8) = k1_funct_1(sK2,X8) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.21/0.50    inference(superposition,[],[f96,f230])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f262,f75])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f261,f35])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f244,f189])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ~v4_relat_1(sK2,k1_xboole_0) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(superposition,[],[f100,f230])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (24646)------------------------------
% 0.21/0.50  % (24646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24646)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (24646)Memory used [KB]: 6268
% 0.21/0.50  % (24646)Time elapsed: 0.045 s
% 0.21/0.50  % (24646)------------------------------
% 0.21/0.50  % (24646)------------------------------
% 0.21/0.50  % (24636)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (24630)Success in time 0.141 s
%------------------------------------------------------------------------------
