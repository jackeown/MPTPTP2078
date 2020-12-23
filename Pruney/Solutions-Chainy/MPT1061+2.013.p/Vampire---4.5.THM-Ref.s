%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 730 expanded)
%              Number of leaves         :   30 ( 219 expanded)
%              Depth                    :   20
%              Number of atoms          :  566 (4286 expanded)
%              Number of equality atoms :  122 ( 466 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f643,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f138,f145,f188,f204,f333,f371,f373,f391,f619,f640])).

fof(f640,plain,
    ( spl5_3
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | spl5_3
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f214,f634])).

fof(f634,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f110,f160])).

fof(f160,plain,(
    ! [X2] : k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) ),
    inference(subsumption_resolution,[],[f151,f55])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
          | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
        & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
        & r1_tarski(sK1,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        & v1_funct_2(X4,sK0,sK3)
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
        | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
      & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      & v1_funct_2(sK4,sK0,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f151,plain,(
    ! [X2] :
      ( k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f57,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f214,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl5_12
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f619,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f617,f400])).

fof(f400,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f376,f398])).

fof(f398,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f186,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f186,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_9
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f376,plain,
    ( m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f178,f219])).

fof(f178,plain,(
    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f164,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f164,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f59,f152])).

fof(f152,plain,(
    ! [X3] : k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3) ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f59,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f617,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f616,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f616,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f606,f578])).

fof(f578,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f524,f569])).

fof(f569,plain,
    ( k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f568,f400])).

fof(f568,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f558,f97])).

fof(f558,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f523,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f523,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f378,f510])).

fof(f510,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f395,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f395,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f387,f97])).

fof(f387,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f348,f219])).

fof(f348,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_12 ),
    inference(resolution,[],[f214,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f378,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f205,f219])).

fof(f205,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f106,f160])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f524,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f380,f510])).

fof(f380,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f222,f219])).

fof(f222,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl5_14
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f606,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f577,f93])).

fof(f93,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f577,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f523,f569])).

fof(f391,plain,
    ( spl5_8
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f377,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f377,plain,
    ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1))
    | spl5_8
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f182,f219])).

fof(f182,plain,
    ( ~ r1_tarski(sK2,k9_relat_1(sK4,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_8
  <=> r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f373,plain,
    ( spl5_13
    | ~ spl5_14
    | spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f372,f213,f104,f221,f217])).

fof(f372,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f345,f205])).

fof(f345,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(resolution,[],[f214,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f371,plain,
    ( ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f369,f58])).

fof(f58,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f369,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(forward_demodulation,[],[f368,f165])).

fof(f165,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f155,f137])).

fof(f137,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_7
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f155,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f368,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f367,f166])).

fof(f166,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f156,f87])).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f156,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f367,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12
    | spl5_14 ),
    inference(trivial_inequality_removal,[],[f366])).

fof(f366,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12
    | spl5_14 ),
    inference(superposition,[],[f365,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f365,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f362,f214])).

fof(f362,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_14 ),
    inference(superposition,[],[f223,f81])).

fof(f223,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f333,plain,
    ( ~ spl5_7
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl5_7
    | spl5_12 ),
    inference(subsumption_resolution,[],[f331,f58])).

fof(f331,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | spl5_12 ),
    inference(forward_demodulation,[],[f330,f165])).

fof(f330,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | spl5_12 ),
    inference(subsumption_resolution,[],[f329,f166])).

fof(f329,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f328,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f328,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_12 ),
    inference(superposition,[],[f295,f77])).

fof(f295,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f294,f164])).

fof(f294,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_12 ),
    inference(forward_demodulation,[],[f293,f169])).

fof(f169,plain,(
    ! [X3] : k9_relat_1(sK4,X3) = k2_relat_1(k7_relat_1(sK4,X3)) ),
    inference(resolution,[],[f166,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f293,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f291,f170])).

fof(f170,plain,(
    ! [X4] : v1_relat_1(k7_relat_1(sK4,X4)) ),
    inference(resolution,[],[f166,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f291,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_12 ),
    inference(resolution,[],[f215,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f215,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f204,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f163,f161])).

fof(f161,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_1 ),
    inference(backward_demodulation,[],[f102,f160])).

fof(f102,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f163,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(backward_demodulation,[],[f158,f160])).

fof(f158,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(subsumption_resolution,[],[f149,f55])).

fof(f149,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f57,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f188,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f177,f184,f180])).

fof(f177,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    inference(resolution,[],[f164,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f145,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f140,f73])).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f140,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f54,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f54,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f138,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f129,f135,f131])).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f128,f57])).

fof(f128,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f56,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f60,f108,f104,f100])).

fof(f60,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:46:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (3866)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (3874)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (3856)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (3857)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (3861)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (3858)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (3864)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (3869)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (3865)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (3882)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (3879)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (3872)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (3862)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (3859)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (3877)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (3860)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (3863)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (3876)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (3881)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (3871)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (3867)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (3873)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (3870)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (3880)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.56  % (3878)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.57  % (3875)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.58  % (3867)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f643,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f111,f138,f145,f188,f204,f333,f371,f373,f391,f619,f640])).
% 0.22/0.58  fof(f640,plain,(
% 0.22/0.58    spl5_3 | ~spl5_12),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f639])).
% 0.22/0.58  fof(f639,plain,(
% 0.22/0.58    $false | (spl5_3 | ~spl5_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f214,f634])).
% 0.22/0.58  fof(f634,plain,(
% 0.22/0.58    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.22/0.58    inference(forward_demodulation,[],[f110,f160])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f151,f55])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    v1_funct_1(sK4)),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f46,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.22/0.58    inference(flattening,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.22/0.58    inference(ennf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.22/0.58    inference(negated_conjecture,[],[f24])).
% 0.22/0.58  fof(f24,conjecture,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) | ~v1_funct_1(sK4)) )),
% 0.22/0.58    inference(resolution,[],[f57,f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.58    inference(flattening,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  fof(f110,plain,(
% 0.22/0.58    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f108])).
% 0.22/0.58  fof(f108,plain,(
% 0.22/0.58    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.58  fof(f214,plain,(
% 0.22/0.58    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f213])).
% 0.22/0.58  fof(f213,plain,(
% 0.22/0.58    spl5_12 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.58  fof(f619,plain,(
% 0.22/0.58    spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f618])).
% 0.22/0.58  fof(f618,plain,(
% 0.22/0.58    $false | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.58    inference(subsumption_resolution,[],[f617,f400])).
% 0.22/0.58  fof(f400,plain,(
% 0.22/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_9 | ~spl5_13)),
% 0.22/0.58    inference(backward_demodulation,[],[f376,f398])).
% 0.22/0.58  fof(f398,plain,(
% 0.22/0.58    k1_xboole_0 = k9_relat_1(sK4,sK1) | (~spl5_9 | ~spl5_13)),
% 0.22/0.58    inference(forward_demodulation,[],[f186,f219])).
% 0.22/0.58  fof(f219,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | ~spl5_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f217])).
% 0.22/0.58  fof(f217,plain,(
% 0.22/0.58    spl5_13 <=> k1_xboole_0 = sK2),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    sK2 = k9_relat_1(sK4,sK1) | ~spl5_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f184])).
% 0.22/0.58  fof(f184,plain,(
% 0.22/0.58    spl5_9 <=> sK2 = k9_relat_1(sK4,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.58  fof(f376,plain,(
% 0.22/0.58    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl5_13),
% 0.22/0.58    inference(backward_demodulation,[],[f178,f219])).
% 0.22/0.58  fof(f178,plain,(
% 0.22/0.58    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2))),
% 0.22/0.58    inference(resolution,[],[f164,f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.58  fof(f164,plain,(
% 0.22/0.58    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f59,f152])).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    ( ! [X3] : (k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3)) )),
% 0.22/0.58    inference(resolution,[],[f57,f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  fof(f617,plain,(
% 0.22/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.58    inference(forward_demodulation,[],[f616,f97])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f53])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.58    inference(flattening,[],[f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.58    inference(nnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.58  fof(f616,plain,(
% 0.22/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.58    inference(subsumption_resolution,[],[f606,f578])).
% 0.22/0.58  fof(f578,plain,(
% 0.22/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.58    inference(backward_demodulation,[],[f524,f569])).
% 0.22/0.58  fof(f569,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(subsumption_resolution,[],[f568,f400])).
% 0.22/0.58  fof(f568,plain,(
% 0.22/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(forward_demodulation,[],[f558,f97])).
% 0.22/0.58  fof(f558,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(resolution,[],[f523,f91])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.22/0.58    inference(equality_resolution,[],[f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(equality_resolution,[],[f72])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.58  fof(f523,plain,(
% 0.22/0.58    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(backward_demodulation,[],[f378,f510])).
% 0.22/0.58  fof(f510,plain,(
% 0.22/0.58    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(resolution,[],[f395,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.58  fof(f395,plain,(
% 0.22/0.58    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(forward_demodulation,[],[f387,f97])).
% 0.22/0.58  fof(f387,plain,(
% 0.22/0.58    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(backward_demodulation,[],[f348,f219])).
% 0.22/0.58  fof(f348,plain,(
% 0.22/0.58    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl5_12),
% 0.22/0.58    inference(resolution,[],[f214,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f48])).
% 0.22/0.58  fof(f378,plain,(
% 0.22/0.58    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl5_2 | ~spl5_13)),
% 0.22/0.58    inference(backward_demodulation,[],[f205,f219])).
% 0.22/0.58  fof(f205,plain,(
% 0.22/0.58    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_2),
% 0.22/0.58    inference(forward_demodulation,[],[f106,f160])).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f104])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.58  fof(f524,plain,(
% 0.22/0.58    sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0) | (~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.58    inference(backward_demodulation,[],[f380,f510])).
% 0.22/0.58  fof(f380,plain,(
% 0.22/0.58    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl5_13 | ~spl5_14)),
% 0.22/0.58    inference(backward_demodulation,[],[f222,f219])).
% 0.22/0.58  fof(f222,plain,(
% 0.22/0.58    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_14),
% 0.22/0.58    inference(avatar_component_clause,[],[f221])).
% 0.22/0.58  fof(f221,plain,(
% 0.22/0.58    spl5_14 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.58  fof(f606,plain,(
% 0.22/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(resolution,[],[f577,f93])).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.58    inference(equality_resolution,[],[f70])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f49])).
% 0.22/0.58  fof(f577,plain,(
% 0.22/0.58    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.22/0.58    inference(backward_demodulation,[],[f523,f569])).
% 0.22/0.58  fof(f391,plain,(
% 0.22/0.58    spl5_8 | ~spl5_13),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f390])).
% 0.22/0.58  fof(f390,plain,(
% 0.22/0.58    $false | (spl5_8 | ~spl5_13)),
% 0.22/0.58    inference(subsumption_resolution,[],[f377,f86])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.58  fof(f377,plain,(
% 0.22/0.58    ~r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) | (spl5_8 | ~spl5_13)),
% 0.22/0.58    inference(backward_demodulation,[],[f182,f219])).
% 0.22/0.58  fof(f182,plain,(
% 0.22/0.58    ~r1_tarski(sK2,k9_relat_1(sK4,sK1)) | spl5_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f180])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    spl5_8 <=> r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.58  fof(f373,plain,(
% 0.22/0.58    spl5_13 | ~spl5_14 | spl5_2 | ~spl5_12),
% 0.22/0.58    inference(avatar_split_clause,[],[f372,f213,f104,f221,f217])).
% 0.22/0.58  fof(f372,plain,(
% 0.22/0.58    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | (spl5_2 | ~spl5_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f345,f205])).
% 0.22/0.58  fof(f345,plain,(
% 0.22/0.58    v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | ~spl5_12),
% 0.22/0.58    inference(resolution,[],[f214,f69])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f49])).
% 0.22/0.58  fof(f371,plain,(
% 0.22/0.58    ~spl5_7 | ~spl5_12 | spl5_14),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f370])).
% 0.22/0.58  fof(f370,plain,(
% 0.22/0.58    $false | (~spl5_7 | ~spl5_12 | spl5_14)),
% 0.22/0.58    inference(subsumption_resolution,[],[f369,f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    r1_tarski(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  fof(f369,plain,(
% 0.22/0.58    ~r1_tarski(sK1,sK0) | (~spl5_7 | ~spl5_12 | spl5_14)),
% 0.22/0.58    inference(forward_demodulation,[],[f368,f165])).
% 0.22/0.58  fof(f165,plain,(
% 0.22/0.58    sK0 = k1_relat_1(sK4) | ~spl5_7),
% 0.22/0.58    inference(forward_demodulation,[],[f155,f137])).
% 0.22/0.58  fof(f137,plain,(
% 0.22/0.58    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f135])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    spl5_7 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 0.22/0.58    inference(resolution,[],[f57,f81])).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.58  fof(f368,plain,(
% 0.22/0.58    ~r1_tarski(sK1,k1_relat_1(sK4)) | (~spl5_12 | spl5_14)),
% 0.22/0.58    inference(subsumption_resolution,[],[f367,f166])).
% 0.22/0.58  fof(f166,plain,(
% 0.22/0.58    v1_relat_1(sK4)),
% 0.22/0.58    inference(subsumption_resolution,[],[f156,f87])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,axiom,(
% 0.22/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.58  fof(f156,plain,(
% 0.22/0.58    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK0,sK3))),
% 0.22/0.58    inference(resolution,[],[f57,f88])).
% 0.22/0.58  fof(f88,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.58  fof(f367,plain,(
% 0.22/0.58    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_12 | spl5_14)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f366])).
% 0.22/0.58  fof(f366,plain,(
% 0.22/0.58    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_12 | spl5_14)),
% 0.22/0.58    inference(superposition,[],[f365,f77])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.58  fof(f365,plain,(
% 0.22/0.58    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_12 | spl5_14)),
% 0.22/0.58    inference(subsumption_resolution,[],[f362,f214])).
% 0.22/0.58  fof(f362,plain,(
% 0.22/0.58    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_14),
% 0.22/0.58    inference(superposition,[],[f223,f81])).
% 0.22/0.58  fof(f223,plain,(
% 0.22/0.58    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | spl5_14),
% 0.22/0.58    inference(avatar_component_clause,[],[f221])).
% 0.22/0.58  fof(f333,plain,(
% 0.22/0.58    ~spl5_7 | spl5_12),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f332])).
% 0.22/0.58  fof(f332,plain,(
% 0.22/0.58    $false | (~spl5_7 | spl5_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f331,f58])).
% 0.22/0.58  fof(f331,plain,(
% 0.22/0.58    ~r1_tarski(sK1,sK0) | (~spl5_7 | spl5_12)),
% 0.22/0.58    inference(forward_demodulation,[],[f330,f165])).
% 0.22/0.58  fof(f330,plain,(
% 0.22/0.58    ~r1_tarski(sK1,k1_relat_1(sK4)) | spl5_12),
% 0.22/0.58    inference(subsumption_resolution,[],[f329,f166])).
% 0.22/0.58  fof(f329,plain,(
% 0.22/0.58    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_12),
% 0.22/0.58    inference(subsumption_resolution,[],[f328,f96])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f74])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(flattening,[],[f50])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f328,plain,(
% 0.22/0.58    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_12),
% 0.22/0.58    inference(superposition,[],[f295,f77])).
% 0.22/0.58  fof(f295,plain,(
% 0.22/0.58    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_12),
% 0.22/0.58    inference(subsumption_resolution,[],[f294,f164])).
% 0.22/0.58  fof(f294,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_12),
% 0.22/0.58    inference(forward_demodulation,[],[f293,f169])).
% 0.22/0.58  fof(f169,plain,(
% 0.22/0.58    ( ! [X3] : (k9_relat_1(sK4,X3) = k2_relat_1(k7_relat_1(sK4,X3))) )),
% 0.22/0.58    inference(resolution,[],[f166,f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.58  fof(f293,plain,(
% 0.22/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_12),
% 0.22/0.58    inference(subsumption_resolution,[],[f291,f170])).
% 0.22/0.58  fof(f170,plain,(
% 0.22/0.58    ( ! [X4] : (v1_relat_1(k7_relat_1(sK4,X4))) )),
% 0.22/0.58    inference(resolution,[],[f166,f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.58  fof(f291,plain,(
% 0.22/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_12),
% 0.22/0.58    inference(resolution,[],[f215,f89])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(flattening,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.58  fof(f215,plain,(
% 0.22/0.58    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f213])).
% 0.22/0.58  fof(f204,plain,(
% 0.22/0.58    spl5_1),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f200])).
% 0.22/0.58  fof(f200,plain,(
% 0.22/0.58    $false | spl5_1),
% 0.22/0.58    inference(resolution,[],[f163,f161])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_1),
% 0.22/0.58    inference(backward_demodulation,[],[f102,f160])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f100])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.58  fof(f163,plain,(
% 0.22/0.58    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 0.22/0.58    inference(backward_demodulation,[],[f158,f160])).
% 0.22/0.58  fof(f158,plain,(
% 0.22/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f149,f55])).
% 0.22/0.58  fof(f149,plain,(
% 0.22/0.58    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) | ~v1_funct_1(sK4)) )),
% 0.22/0.58    inference(resolution,[],[f57,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.58    inference(flattening,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.22/0.58  fof(f188,plain,(
% 0.22/0.58    ~spl5_8 | spl5_9),
% 0.22/0.58    inference(avatar_split_clause,[],[f177,f184,f180])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    sK2 = k9_relat_1(sK4,sK1) | ~r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 0.22/0.58    inference(resolution,[],[f164,f76])).
% 0.22/0.58  fof(f76,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f51])).
% 0.22/0.58  fof(f145,plain,(
% 0.22/0.58    ~spl5_6),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f144])).
% 0.22/0.58  fof(f144,plain,(
% 0.22/0.58    $false | ~spl5_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f140,f73])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl5_6),
% 0.22/0.58    inference(backward_demodulation,[],[f54,f133])).
% 0.22/0.58  fof(f133,plain,(
% 0.22/0.58    k1_xboole_0 = sK3 | ~spl5_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f131])).
% 0.22/0.58  fof(f131,plain,(
% 0.22/0.58    spl5_6 <=> k1_xboole_0 = sK3),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ~v1_xboole_0(sK3)),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  fof(f138,plain,(
% 0.22/0.58    spl5_6 | spl5_7),
% 0.22/0.58    inference(avatar_split_clause,[],[f129,f135,f131])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3),
% 0.22/0.58    inference(subsumption_resolution,[],[f128,f57])).
% 0.22/0.58  fof(f128,plain,(
% 0.22/0.58    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.22/0.58    inference(resolution,[],[f56,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f49])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    v1_funct_2(sK4,sK0,sK3)),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f60,f108,f104,f100])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f47])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (3867)------------------------------
% 0.22/0.58  % (3867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3867)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (3867)Memory used [KB]: 11001
% 0.22/0.58  % (3867)Time elapsed: 0.141 s
% 0.22/0.58  % (3867)------------------------------
% 0.22/0.58  % (3867)------------------------------
% 1.79/0.60  % (3855)Success in time 0.237 s
%------------------------------------------------------------------------------
