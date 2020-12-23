%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1035+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 (29426 expanded)
%              Number of leaves         :   11 (8535 expanded)
%              Depth                    :   38
%              Number of atoms          :  548 (287623 expanded)
%              Number of equality atoms :  166 (92014 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(subsumption_resolution,[],[f266,f263])).

fof(f263,plain,(
    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f254,f256,f68])).

fof(f68,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(sK2))
      | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | r1_partfun1(sK2,sK3) ) ),
    inference(backward_demodulation,[],[f38,f60])).

fof(f60,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f33,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f38,plain,(
    ! [X5] :
      ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f256,plain,(
    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f61,f32,f166,f254,f222])).

fof(f222,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
      | r1_partfun1(X5,sK3)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f221,f75])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f221,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
      | r1_partfun1(X5,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f212,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f212,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
      | r1_partfun1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f42,f205])).

fof(f205,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f173,f192])).

fof(f192,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(unit_resulting_resolution,[],[f169,f170,f58])).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f170,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f156,f161])).

fof(f161,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f153,f37])).

fof(f37,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f153,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f131,f143,f152])).

fof(f152,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f151,f143])).

fof(f151,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f150,f61])).

fof(f150,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f144,f32])).

fof(f144,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f112,f84])).

fof(f84,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f59,f60])).

fof(f59,plain,(
    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f112,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3))
      | r1_partfun1(X6,sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f111,f75])).

fof(f111,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3))
      | r1_partfun1(X6,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f101,f34])).

fof(f101,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3))
      | r1_partfun1(X6,sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f43,f91])).

fof(f91,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f83,f74])).

fof(f74,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f36,f46])).

fof(f83,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f143,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f140,f40])).

fof(f40,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1
    | ~ r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f139,f69])).

fof(f69,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(backward_demodulation,[],[f39,f60])).

fof(f39,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f138,f68])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f137,f61])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_relat_1(sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f134,f32])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f104,f84])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK3)
      | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f103,f75])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK3)
      | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK3)
      | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f41,f91])).

fof(f41,plain,(
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

fof(f131,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f123,f68])).

fof(f123,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f122,f61])).

fof(f122,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f118,f32])).

fof(f118,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f108,f84])).

fof(f108,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
      | r1_partfun1(X4,sK3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f107,f75])).

fof(f107,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
      | r1_partfun1(X4,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f99,f34])).

fof(f99,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
      | r1_partfun1(X4,sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f42,f91])).

fof(f156,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f36,f153])).

fof(f169,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f155,f161])).

fof(f155,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f153])).

fof(f173,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f159,f161])).

fof(f159,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f74,f153])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f166,plain,(
    r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f84,f161])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f33,f45])).

fof(f254,plain,(
    ~ r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f252,f40])).

fof(f252,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f251,f69])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f250,f68])).

fof(f250,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f249,f61])).

fof(f249,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f247,f32])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r1_partfun1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f218,f166])).

fof(f218,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK3)
      | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f217,f75])).

fof(f217,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK3)
      | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f210,f34])).

fof(f210,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK3)
      | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f41,f205])).

fof(f266,plain,(
    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f61,f32,f254,f166,f226])).

fof(f226,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3))
      | r1_partfun1(X7,sK3)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f225,f75])).

fof(f225,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3))
      | r1_partfun1(X7,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f214,f34])).

fof(f214,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3))
      | r1_partfun1(X7,sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f43,f205])).

%------------------------------------------------------------------------------
