%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 (13699 expanded)
%              Number of leaves         :   11 (3961 expanded)
%              Depth                    :   39
%              Number of atoms          :  544 (113853 expanded)
%              Number of equality atoms :  147 (23124 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(global_subsumption,[],[f234,f248,f254])).

% (23659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f254,plain,(
    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f253,f60])).

fof(f60,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f33,f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
   => ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
      & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_2)).

fof(f253,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f252,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f252,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f249,f248])).

fof(f249,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f213,f164])).

fof(f164,plain,(
    r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f83,f154])).

fof(f154,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f153,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f142,f129])).

fof(f129,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f122,f67])).

fof(f67,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | r1_partfun1(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f37,f59])).

fof(f59,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f33,f45])).

fof(f45,plain,(
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

fof(f37,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f121,f60])).

fof(f121,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f117,f32])).

fof(f117,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f107,f83])).

fof(f107,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK4(X4,sK2),k1_relat_1(X4))
      | r1_partfun1(X4,sK2)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f106,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f44])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK4(X4,sK2),k1_relat_1(X4))
      | r1_partfun1(X4,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f98,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | r2_hidden(sK4(X4,sK2),k1_relat_1(X4))
      | r1_partfun1(X4,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f41,f90])).

fof(f90,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f82,f73])).

fof(f73,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f45])).

fof(f82,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f142,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f139,f39])).

% (23658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f39,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f139,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f138,f68])).

fof(f68,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(backward_demodulation,[],[f38,f59])).

fof(f38,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f137,f67])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f136,f60])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_relat_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f133,f32])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f103,f83])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK2)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f102,f74])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_partfun1(X0,sK2)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,(
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
    inference(superposition,[],[f40,f90])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f153,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f152,f142])).

fof(f152,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f151,f60])).

fof(f151,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f145,f32])).

fof(f145,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f111,f83])).

fof(f111,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2))
      | r1_partfun1(X6,sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f110,f74])).

fof(f110,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2))
      | r1_partfun1(X6,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f100,plain,(
    ! [X6] :
      ( ~ r1_tarski(k1_relat_1(X6),sK0)
      | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2))
      | r1_partfun1(X6,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f42,f90])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f69,f43])).

fof(f43,plain,(
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
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f58,f59])).

fof(f58,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f46])).

fof(f46,plain,(
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

fof(f213,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2))
      | r1_partfun1(X7,sK2)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f212,f74])).

fof(f212,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2))
      | r1_partfun1(X7,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f201,f34])).

fof(f201,plain,(
    ! [X7] :
      ( ~ r1_tarski(k1_relat_1(X7),k1_xboole_0)
      | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2))
      | r1_partfun1(X7,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f42,f192])).

fof(f192,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f161,f179])).

fof(f179,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(unit_resulting_resolution,[],[f156,f157,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f157,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f36,f154])).

fof(f156,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f154])).

fof(f161,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f73,f154])).

fof(f248,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f246,f39])).

fof(f246,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f240,f68])).

fof(f240,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f239,f67])).

fof(f239,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f238,f60])).

fof(f238,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f236,f32])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r1_partfun1(sK1,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f205,f164])).

fof(f205,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK2)
      | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f204,f74])).

fof(f204,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK2)
      | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f197,f34])).

fof(f197,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r1_partfun1(X2,sK2)
      | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f40,f192])).

fof(f234,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f229,f67])).

fof(f229,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f228,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f226,f32])).

fof(f226,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f209,f164])).

fof(f209,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK4(X5,sK2),k1_relat_1(X5))
      | r1_partfun1(X5,sK2)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f208,f74])).

fof(f208,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK4(X5,sK2),k1_relat_1(X5))
      | r1_partfun1(X5,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f199,f34])).

fof(f199,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k1_xboole_0)
      | r2_hidden(sK4(X5,sK2),k1_relat_1(X5))
      | r1_partfun1(X5,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f41,f192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:41:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (23671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (23669)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (23661)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (23665)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (23671)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(global_subsumption,[],[f234,f248,f254])).
% 0.22/0.50  % (23659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f253,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f33,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    (((k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) => (k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.22/0.50    inference(rectify,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_2)).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f252,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v1_funct_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f249,f248])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f213,f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f83,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f153,f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f143])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.50    inference(resolution,[],[f142,f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f122,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK1)) | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | r1_partfun1(sK1,sK2)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f37,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f33,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) | r1_partfun1(sK1,sK2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f121,f60])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f32])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(resolution,[],[f107,f83])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK4(X4,sK2),k1_relat_1(X4)) | r1_partfun1(X4,sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f36,f44])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK4(X4,sK2),k1_relat_1(X4)) | r1_partfun1(X4,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f98,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK4(X4,sK2),k1_relat_1(X4)) | r1_partfun1(X4,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(superposition,[],[f41,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f82,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f36,f45])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK0,sK2) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f76,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f36,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f139,f39])).
% 0.22/0.50  % (23658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0 | ~r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f138,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(backward_demodulation,[],[f38,f59])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) | ~r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f137,f67])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f136,f60])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f133,f32])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(resolution,[],[f103,f83])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK2) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f74])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK2) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f34])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK2) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(superposition,[],[f40,f90])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f152,f142])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f151,f60])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f145,f32])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(resolution,[],[f111,f83])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2)) | r1_partfun1(X6,sK2) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f74])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2)) | r1_partfun1(X6,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f34])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),sK0) | k1_funct_1(X6,sK4(X6,sK2)) != k1_funct_1(sK2,sK4(X6,sK2)) | r1_partfun1(X6,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(superposition,[],[f42,f90])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f69,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(forward_demodulation,[],[f58,f59])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f33,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),k1_xboole_0) | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2)) | r1_partfun1(X7,sK2) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f212,f74])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),k1_xboole_0) | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2)) | r1_partfun1(X7,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f201,f34])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),k1_xboole_0) | k1_funct_1(X7,sK4(X7,sK2)) != k1_funct_1(sK2,sK4(X7,sK2)) | r1_partfun1(X7,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.22/0.50    inference(superposition,[],[f42,f192])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.50    inference(backward_demodulation,[],[f161,f179])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f156,f157,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f36,f154])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f35,f154])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.22/0.50    inference(backward_demodulation,[],[f73,f154])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ~r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f246,f39])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f240,f68])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f239,f67])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f238,f60])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f236,f32])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.50    inference(resolution,[],[f205,f164])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r1_partfun1(X2,sK2) | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f204,f74])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r1_partfun1(X2,sK2) | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3) | ~v1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f197,f34])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),k1_xboole_0) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r1_partfun1(X2,sK2) | k1_funct_1(X2,X3) = k1_funct_1(sK2,X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(superposition,[],[f40,f192])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f233])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f229,f67])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f228,f60])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f226,f32])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f209,f164])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k1_xboole_0) | r2_hidden(sK4(X5,sK2),k1_relat_1(X5)) | r1_partfun1(X5,sK2) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f208,f74])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k1_xboole_0) | r2_hidden(sK4(X5,sK2),k1_relat_1(X5)) | r1_partfun1(X5,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f199,f34])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k1_xboole_0) | r2_hidden(sK4(X5,sK2),k1_relat_1(X5)) | r1_partfun1(X5,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.22/0.50    inference(superposition,[],[f41,f192])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (23671)------------------------------
% 0.22/0.50  % (23671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23671)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (23671)Memory used [KB]: 6268
% 0.22/0.50  % (23671)Time elapsed: 0.017 s
% 0.22/0.50  % (23671)------------------------------
% 0.22/0.50  % (23671)------------------------------
% 0.22/0.50  % (23652)Success in time 0.139 s
%------------------------------------------------------------------------------
