%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:13 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  141 (5331 expanded)
%              Number of leaves         :   17 (1540 expanded)
%              Depth                    :   39
%              Number of atoms          :  478 (29527 expanded)
%              Number of equality atoms :  134 (4817 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f561,plain,(
    $false ),
    inference(subsumption_resolution,[],[f557,f130])).

fof(f130,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f51,f128])).

fof(f128,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f51,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f557,plain,(
    ~ r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f503,f175])).

fof(f175,plain,(
    ~ r2_hidden(sK7(sK4,sK2,sK3),k1_xboole_0) ),
    inference(resolution,[],[f174,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f174,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ r2_hidden(sK7(sK4,sK2,sK3),X0) ) ),
    inference(subsumption_resolution,[],[f173,f90])).

fof(f90,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f50])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,sK2,sK3),X0)
      | ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f171,f130])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,sK2,sK3),X0)
      | ~ r1_tarski(X0,sK0)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f147,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK2)
      | ~ r2_hidden(sK7(sK4,sK2,sK3),X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f146,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f146,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ r2_hidden(sK7(sK4,sK2,sK3),sK0) ),
    inference(superposition,[],[f52,f142])).

fof(f142,plain,(
    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) ),
    inference(resolution,[],[f137,f130])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | k1_funct_1(sK3,sK7(X0,X1,sK3)) = X0 ) ),
    inference(resolution,[],[f135,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | k1_funct_1(sK3,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f117,f90])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | k1_funct_1(sK3,X0) = X1
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f135,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK7(X4,X5,sK3),X4),sK3)
      | ~ r2_hidden(X4,k9_relat_1(sK3,X5)) ) ),
    inference(resolution,[],[f68,f90])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f503,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK7(X2,X3,sK3),k1_xboole_0)
      | ~ r2_hidden(X2,k9_relat_1(sK3,X3)) ) ),
    inference(backward_demodulation,[],[f138,f499])).

fof(f499,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f498,f79])).

fof(f498,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f477,f463])).

fof(f463,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f462,f324])).

fof(f324,plain,
    ( r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f130,f297])).

fof(f297,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f296,f290])).

fof(f290,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f86,f287])).

fof(f287,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f285,f130])).

fof(f285,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f277,f176])).

fof(f176,plain,(
    ~ r2_hidden(sK7(sK4,sK2,sK3),sK0) ),
    inference(resolution,[],[f174,f89])).

fof(f89,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f73,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f277,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK3),sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f138,f275])).

fof(f275,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f274,f112])).

fof(f112,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f274,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f272,f49])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f272,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f60,f50])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f86,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f75,f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f296,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f288,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f83,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f288,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f49,f287])).

fof(f462,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f457])).

fof(f457,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f443,f336])).

fof(f336,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f175,f297])).

fof(f443,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f327,f430])).

fof(f430,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f428])).

fof(f428,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f426,f227])).

fof(f227,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,k1_xboole_0),X0)
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f224,f114])).

fof(f114,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f113,f79])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | k1_relat_1(X0) = k1_relset_1(X1,X2,X0) ) ),
    inference(resolution,[],[f66,f76])).

fof(f224,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
      | r2_hidden(sK6(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f222,f79])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X0,X2))
      | k1_relset_1(X0,X2,X1) = X0
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(resolution,[],[f57,f76])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | r2_hidden(sK6(X1,X2),X1)
      | k1_relset_1(X1,X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
            & r2_hidden(sK6(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f36,f35])).

fof(f35,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
        & r2_hidden(sK6(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f426,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(X0,k1_xboole_0),k1_xboole_0)
      | k1_xboole_0 = sK0
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f396,f79])).

fof(f396,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 = sK0
      | ~ r2_hidden(sK6(X0,k1_xboole_0),X1)
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f353,f71])).

fof(f353,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f352,f114])).

fof(f352,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(k1_xboole_0))
      | k1_relset_1(X0,X1,k1_xboole_0) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f348,f79])).

fof(f348,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,k1_xboole_0) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f269,f297])).

fof(f269,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,sK3),k1_relat_1(sK3))
      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,sK3) = X0 ) ),
    inference(resolution,[],[f252,f156])).

fof(f156,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f155,f90])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f80,f48])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f252,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X1,X2),X3),X2)
      | k1_relset_1(X1,X4,X2) = X1
      | ~ r1_tarski(X2,k2_zfmisc_1(X1,X4)) ) ),
    inference(resolution,[],[f58,f76])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
      | k1_relset_1(X1,X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f327,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,k1_xboole_0),k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f138,f297])).

fof(f477,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f259,f463])).

fof(f259,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f256,f223])).

fof(f223,plain,
    ( r2_hidden(sK6(sK0,sK3),sK0)
    | sK0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f221,f112])).

fof(f221,plain,
    ( r2_hidden(sK6(sK0,sK3),sK0)
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f57,f50])).

fof(f256,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK0,sK3),X0)
      | sK0 = k1_relat_1(sK3)
      | ~ r1_tarski(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f254,f71])).

fof(f254,plain,
    ( ~ r2_hidden(sK6(sK0,sK3),k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f253,f156])).

fof(f253,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK6(sK0,sK3),X0),sK3)
      | sK0 = k1_relat_1(sK3) ) ),
    inference(forward_demodulation,[],[f251,f112])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK6(sK0,sK3),X0),sK3)
      | sK0 = k1_relset_1(sK0,sK1,sK3) ) ),
    inference(resolution,[],[f58,f50])).

fof(f138,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK7(X2,X3,sK3),k1_relat_1(sK3))
      | ~ r2_hidden(X2,k9_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f135,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f108,f90])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (27561)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (27542)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (27553)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (27551)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (27545)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (27567)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.53  % (27543)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.53  % (27563)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.53  % (27541)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (27540)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (27539)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  % (27538)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (27559)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (27566)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.54  % (27565)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.54  % (27564)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.54  % (27555)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (27550)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (27557)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (27562)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (27548)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (27547)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (27548)Refutation not found, incomplete strategy% (27548)------------------------------
% 1.43/0.55  % (27548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (27548)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (27548)Memory used [KB]: 10746
% 1.43/0.55  % (27548)Time elapsed: 0.150 s
% 1.43/0.55  % (27548)------------------------------
% 1.43/0.55  % (27548)------------------------------
% 1.43/0.55  % (27558)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (27556)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (27546)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  % (27549)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (27549)Refutation not found, incomplete strategy% (27549)------------------------------
% 1.43/0.56  % (27549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (27549)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (27549)Memory used [KB]: 10746
% 1.43/0.56  % (27549)Time elapsed: 0.160 s
% 1.43/0.56  % (27549)------------------------------
% 1.43/0.56  % (27549)------------------------------
% 1.43/0.56  % (27560)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.56  % (27554)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (27544)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.58  % (27543)Refutation found. Thanks to Tanya!
% 1.43/0.58  % SZS status Theorem for theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f561,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(subsumption_resolution,[],[f557,f130])).
% 1.43/0.58  fof(f130,plain,(
% 1.43/0.58    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.43/0.58    inference(backward_demodulation,[],[f51,f128])).
% 1.43/0.58  fof(f128,plain,(
% 1.43/0.58    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.43/0.58    inference(resolution,[],[f53,f50])).
% 1.43/0.58  fof(f50,plain,(
% 1.43/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.58    inference(cnf_transformation,[],[f30])).
% 1.43/0.58  fof(f30,plain,(
% 1.43/0.58    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f29,f28])).
% 1.43/0.58  fof(f28,plain,(
% 1.43/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f29,plain,(
% 1.43/0.58    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f16,plain,(
% 1.43/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.43/0.58    inference(flattening,[],[f15])).
% 1.43/0.58  fof(f15,plain,(
% 1.43/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.43/0.58    inference(ennf_transformation,[],[f14])).
% 1.43/0.58  fof(f14,negated_conjecture,(
% 1.43/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.43/0.58    inference(negated_conjecture,[],[f13])).
% 1.43/0.58  fof(f13,conjecture,(
% 1.43/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 1.43/0.58  fof(f53,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f17])).
% 1.43/0.58  fof(f17,plain,(
% 1.43/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.58    inference(ennf_transformation,[],[f10])).
% 1.43/0.58  fof(f10,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.43/0.58  fof(f51,plain,(
% 1.43/0.58    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.43/0.58    inference(cnf_transformation,[],[f30])).
% 1.43/0.58  fof(f557,plain,(
% 1.43/0.58    ~r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.43/0.58    inference(resolution,[],[f503,f175])).
% 1.43/0.58  fof(f175,plain,(
% 1.43/0.58    ~r2_hidden(sK7(sK4,sK2,sK3),k1_xboole_0)),
% 1.43/0.58    inference(resolution,[],[f174,f79])).
% 1.43/0.58  fof(f79,plain,(
% 1.43/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f2])).
% 1.43/0.58  fof(f2,axiom,(
% 1.43/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.43/0.58  fof(f174,plain,(
% 1.43/0.58    ( ! [X0] : (~r1_tarski(X0,sK0) | ~r2_hidden(sK7(sK4,sK2,sK3),X0)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f173,f90])).
% 1.43/0.58  fof(f90,plain,(
% 1.43/0.58    v1_relat_1(sK3)),
% 1.43/0.58    inference(resolution,[],[f74,f50])).
% 1.43/0.58  fof(f74,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f26])).
% 1.43/0.58  fof(f26,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.58    inference(ennf_transformation,[],[f8])).
% 1.43/0.58  fof(f8,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.43/0.58  fof(f173,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK7(sK4,sK2,sK3),X0) | ~r1_tarski(X0,sK0) | ~v1_relat_1(sK3)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f171,f130])).
% 1.43/0.58  fof(f171,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK7(sK4,sK2,sK3),X0) | ~r1_tarski(X0,sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~v1_relat_1(sK3)) )),
% 1.43/0.58    inference(resolution,[],[f147,f69])).
% 1.43/0.58  fof(f69,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f42])).
% 1.43/0.58  fof(f42,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 1.43/0.58  fof(f41,plain,(
% 1.43/0.58    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f40,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(rectify,[],[f39])).
% 1.43/0.58  fof(f39,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(nnf_transformation,[],[f24])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(ennf_transformation,[],[f6])).
% 1.43/0.58  fof(f6,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.43/0.58  fof(f147,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~r2_hidden(sK7(sK4,sK2,sK3),X0) | ~r1_tarski(X0,sK0)) )),
% 1.43/0.58    inference(resolution,[],[f146,f71])).
% 1.43/0.58  fof(f71,plain,(
% 1.43/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f46])).
% 1.43/0.58  fof(f46,plain,(
% 1.43/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).
% 1.43/0.58  fof(f45,plain,(
% 1.43/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f44,plain,(
% 1.43/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.58    inference(rectify,[],[f43])).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.58    inference(nnf_transformation,[],[f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f1])).
% 1.43/0.58  fof(f1,axiom,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.58  fof(f146,plain,(
% 1.43/0.58    ~r2_hidden(sK7(sK4,sK2,sK3),sK0) | ~r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 1.43/0.58    inference(trivial_inequality_removal,[],[f145])).
% 1.43/0.58  fof(f145,plain,(
% 1.43/0.58    sK4 != sK4 | ~r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~r2_hidden(sK7(sK4,sK2,sK3),sK0)),
% 1.43/0.58    inference(superposition,[],[f52,f142])).
% 1.43/0.58  fof(f142,plain,(
% 1.43/0.58    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))),
% 1.43/0.58    inference(resolution,[],[f137,f130])).
% 1.43/0.58  fof(f137,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(X0,X1,sK3)) = X0) )),
% 1.43/0.58    inference(resolution,[],[f135,f118])).
% 1.43/0.58  fof(f118,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f117,f90])).
% 1.43/0.58  fof(f117,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 | ~v1_relat_1(sK3)) )),
% 1.43/0.58    inference(resolution,[],[f55,f48])).
% 1.43/0.58  fof(f48,plain,(
% 1.43/0.58    v1_funct_1(sK3)),
% 1.43/0.58    inference(cnf_transformation,[],[f30])).
% 1.43/0.58  fof(f55,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f32])).
% 1.43/0.58  fof(f32,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(flattening,[],[f31])).
% 1.43/0.58  fof(f31,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(nnf_transformation,[],[f19])).
% 1.43/0.58  fof(f19,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.43/0.58    inference(flattening,[],[f18])).
% 1.43/0.58  fof(f18,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.43/0.58    inference(ennf_transformation,[],[f7])).
% 1.43/0.58  fof(f7,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.43/0.58  fof(f135,plain,(
% 1.43/0.58    ( ! [X4,X5] : (r2_hidden(k4_tarski(sK7(X4,X5,sK3),X4),sK3) | ~r2_hidden(X4,k9_relat_1(sK3,X5))) )),
% 1.43/0.58    inference(resolution,[],[f68,f90])).
% 1.43/0.58  fof(f68,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f42])).
% 1.43/0.58  fof(f52,plain,(
% 1.43/0.58    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f30])).
% 1.43/0.58  fof(f503,plain,(
% 1.43/0.58    ( ! [X2,X3] : (r2_hidden(sK7(X2,X3,sK3),k1_xboole_0) | ~r2_hidden(X2,k9_relat_1(sK3,X3))) )),
% 1.43/0.58    inference(backward_demodulation,[],[f138,f499])).
% 1.43/0.58  fof(f499,plain,(
% 1.43/0.58    k1_xboole_0 = k1_relat_1(sK3)),
% 1.43/0.58    inference(subsumption_resolution,[],[f498,f79])).
% 1.43/0.58  fof(f498,plain,(
% 1.43/0.58    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.43/0.58    inference(forward_demodulation,[],[f477,f463])).
% 1.43/0.58  fof(f463,plain,(
% 1.43/0.58    k1_xboole_0 = sK0),
% 1.43/0.58    inference(subsumption_resolution,[],[f462,f324])).
% 1.43/0.58  fof(f324,plain,(
% 1.43/0.58    r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | k1_xboole_0 = sK0),
% 1.43/0.58    inference(superposition,[],[f130,f297])).
% 1.43/0.58  fof(f297,plain,(
% 1.43/0.58    k1_xboole_0 = sK3 | k1_xboole_0 = sK0),
% 1.43/0.58    inference(subsumption_resolution,[],[f296,f290])).
% 1.43/0.58  fof(f290,plain,(
% 1.43/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.43/0.58    inference(backward_demodulation,[],[f86,f287])).
% 1.43/0.58  fof(f287,plain,(
% 1.43/0.58    k1_xboole_0 = sK1),
% 1.43/0.58    inference(subsumption_resolution,[],[f285,f130])).
% 1.43/0.58  fof(f285,plain,(
% 1.43/0.58    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | k1_xboole_0 = sK1),
% 1.43/0.58    inference(resolution,[],[f277,f176])).
% 1.43/0.58  fof(f176,plain,(
% 1.43/0.58    ~r2_hidden(sK7(sK4,sK2,sK3),sK0)),
% 1.43/0.58    inference(resolution,[],[f174,f89])).
% 1.43/0.58  fof(f89,plain,(
% 1.43/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f88])).
% 1.43/0.58  fof(f88,plain,(
% 1.43/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.43/0.58    inference(resolution,[],[f73,f72])).
% 1.43/0.58  fof(f72,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f46])).
% 1.43/0.58  fof(f73,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f46])).
% 1.43/0.58  fof(f277,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK3),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_xboole_0 = sK1) )),
% 1.43/0.58    inference(superposition,[],[f138,f275])).
% 1.43/0.58  fof(f275,plain,(
% 1.43/0.58    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.43/0.58    inference(superposition,[],[f274,f112])).
% 1.43/0.58  fof(f112,plain,(
% 1.43/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.43/0.58    inference(resolution,[],[f66,f50])).
% 1.43/0.58  fof(f66,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f23])).
% 1.43/0.58  fof(f23,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.58    inference(ennf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.43/0.58  fof(f274,plain,(
% 1.43/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.43/0.58    inference(subsumption_resolution,[],[f272,f49])).
% 1.43/0.58  fof(f49,plain,(
% 1.43/0.58    v1_funct_2(sK3,sK0,sK1)),
% 1.43/0.58    inference(cnf_transformation,[],[f30])).
% 1.43/0.58  fof(f272,plain,(
% 1.43/0.58    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.43/0.58    inference(resolution,[],[f60,f50])).
% 1.43/0.58  fof(f60,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.43/0.58    inference(cnf_transformation,[],[f38])).
% 1.43/0.58  fof(f38,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.58    inference(nnf_transformation,[],[f22])).
% 1.43/0.58  fof(f22,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.58    inference(flattening,[],[f21])).
% 1.43/0.58  fof(f21,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.58    inference(ennf_transformation,[],[f12])).
% 1.43/0.58  fof(f12,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.43/0.58  fof(f86,plain,(
% 1.43/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.43/0.58    inference(resolution,[],[f75,f50])).
% 1.43/0.58  fof(f75,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f47])).
% 1.43/0.58  fof(f47,plain,(
% 1.43/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.43/0.58    inference(nnf_transformation,[],[f3])).
% 1.43/0.58  fof(f3,axiom,(
% 1.43/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.43/0.58  fof(f296,plain,(
% 1.43/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.43/0.58    inference(resolution,[],[f288,f181])).
% 1.43/0.58  fof(f181,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v1_funct_2(X0,X1,k1_xboole_0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.43/0.58    inference(resolution,[],[f83,f76])).
% 1.43/0.58  fof(f76,plain,(
% 1.43/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f47])).
% 1.43/0.58  fof(f83,plain,(
% 1.43/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.43/0.58    inference(equality_resolution,[],[f64])).
% 1.43/0.58  fof(f64,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f38])).
% 1.43/0.58  fof(f288,plain,(
% 1.43/0.58    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.43/0.58    inference(backward_demodulation,[],[f49,f287])).
% 1.43/0.58  fof(f462,plain,(
% 1.43/0.58    ~r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | k1_xboole_0 = sK0),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f457])).
% 1.43/0.58  fof(f457,plain,(
% 1.43/0.58    ~r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.43/0.58    inference(resolution,[],[f443,f336])).
% 1.43/0.58  fof(f336,plain,(
% 1.43/0.58    ~r2_hidden(sK7(sK4,sK2,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0),
% 1.43/0.58    inference(superposition,[],[f175,f297])).
% 1.43/0.58  fof(f443,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) | k1_xboole_0 = sK0) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f431])).
% 1.43/0.58  fof(f431,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0) )),
% 1.43/0.58    inference(superposition,[],[f327,f430])).
% 1.43/0.58  fof(f430,plain,(
% 1.43/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK0),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f428])).
% 1.43/0.58  fof(f428,plain,(
% 1.43/0.58    k1_xboole_0 = sK0 | k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/0.58    inference(resolution,[],[f426,f227])).
% 1.43/0.58  fof(f227,plain,(
% 1.43/0.58    ( ! [X0] : (r2_hidden(sK6(X0,k1_xboole_0),X0) | k1_relat_1(k1_xboole_0) = X0) )),
% 1.43/0.58    inference(forward_demodulation,[],[f224,f114])).
% 1.43/0.58  fof(f114,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.43/0.58    inference(resolution,[],[f113,f79])).
% 1.43/0.58  fof(f113,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | k1_relat_1(X0) = k1_relset_1(X1,X2,X0)) )),
% 1.43/0.58    inference(resolution,[],[f66,f76])).
% 1.43/0.58  fof(f224,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = X0 | r2_hidden(sK6(X0,k1_xboole_0),X0)) )),
% 1.43/0.58    inference(resolution,[],[f222,f79])).
% 1.43/0.58  fof(f222,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(X0,X2)) | k1_relset_1(X0,X2,X1) = X0 | r2_hidden(sK6(X0,X1),X0)) )),
% 1.43/0.58    inference(resolution,[],[f57,f76])).
% 1.43/0.58  fof(f57,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r2_hidden(sK6(X1,X2),X1) | k1_relset_1(X1,X0,X2) = X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f37])).
% 1.43/0.58  fof(f37,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f36,f35])).
% 1.43/0.58  fof(f35,plain,(
% 1.43/0.58    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f36,plain,(
% 1.43/0.58    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f34,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.43/0.58    inference(rectify,[],[f33])).
% 1.43/0.58  fof(f33,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.43/0.58    inference(nnf_transformation,[],[f20])).
% 1.43/0.58  fof(f20,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.43/0.58    inference(ennf_transformation,[],[f11])).
% 1.43/0.58  fof(f11,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.43/0.58  fof(f426,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK6(X0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0 | k1_relat_1(k1_xboole_0) = X0) )),
% 1.43/0.58    inference(resolution,[],[f396,f79])).
% 1.43/0.58  fof(f396,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = sK0 | ~r2_hidden(sK6(X0,k1_xboole_0),X1) | k1_relat_1(k1_xboole_0) = X0) )),
% 1.43/0.58    inference(resolution,[],[f353,f71])).
% 1.43/0.58  fof(f353,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X0 | k1_xboole_0 = sK0) )),
% 1.43/0.58    inference(forward_demodulation,[],[f352,f114])).
% 1.43/0.58  fof(f352,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_relset_1(X0,X1,k1_xboole_0) = X0 | k1_xboole_0 = sK0) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f348,f79])).
% 1.43/0.58  fof(f348,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,k1_xboole_0) = X0 | k1_xboole_0 = sK0) )),
% 1.43/0.58    inference(superposition,[],[f269,f297])).
% 1.43/0.58  fof(f269,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X0,sK3),k1_relat_1(sK3)) | ~r1_tarski(sK3,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,sK3) = X0) )),
% 1.43/0.58    inference(resolution,[],[f252,f156])).
% 1.43/0.58  fof(f156,plain,(
% 1.43/0.58    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f155,f90])).
% 1.43/0.58  fof(f155,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~v1_relat_1(sK3)) )),
% 1.43/0.58    inference(resolution,[],[f80,f48])).
% 1.43/0.58  fof(f80,plain,(
% 1.43/0.58    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.43/0.58    inference(equality_resolution,[],[f56])).
% 1.43/0.58  fof(f56,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f32])).
% 1.43/0.58  fof(f252,plain,(
% 1.43/0.58    ( ! [X4,X2,X3,X1] : (~r2_hidden(k4_tarski(sK6(X1,X2),X3),X2) | k1_relset_1(X1,X4,X2) = X1 | ~r1_tarski(X2,k2_zfmisc_1(X1,X4))) )),
% 1.43/0.58    inference(resolution,[],[f58,f76])).
% 1.43/0.58  fof(f58,plain,(
% 1.43/0.58    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) | k1_relset_1(X1,X0,X2) = X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f37])).
% 1.43/0.58  fof(f327,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) | k1_xboole_0 = sK0) )),
% 1.43/0.58    inference(superposition,[],[f138,f297])).
% 1.43/0.58  fof(f477,plain,(
% 1.43/0.58    k1_xboole_0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3))),
% 1.43/0.58    inference(backward_demodulation,[],[f259,f463])).
% 1.43/0.58  fof(f259,plain,(
% 1.43/0.58    ~r1_tarski(sK0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f257])).
% 1.43/0.58  fof(f257,plain,(
% 1.43/0.58    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.43/0.58    inference(resolution,[],[f256,f223])).
% 1.43/0.58  fof(f223,plain,(
% 1.43/0.58    r2_hidden(sK6(sK0,sK3),sK0) | sK0 = k1_relat_1(sK3)),
% 1.43/0.58    inference(forward_demodulation,[],[f221,f112])).
% 1.43/0.58  fof(f221,plain,(
% 1.43/0.58    r2_hidden(sK6(sK0,sK3),sK0) | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.43/0.58    inference(resolution,[],[f57,f50])).
% 1.43/0.58  fof(f256,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK6(sK0,sK3),X0) | sK0 = k1_relat_1(sK3) | ~r1_tarski(X0,k1_relat_1(sK3))) )),
% 1.43/0.58    inference(resolution,[],[f254,f71])).
% 1.43/0.58  fof(f254,plain,(
% 1.43/0.58    ~r2_hidden(sK6(sK0,sK3),k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 1.43/0.58    inference(resolution,[],[f253,f156])).
% 1.43/0.58  fof(f253,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK6(sK0,sK3),X0),sK3) | sK0 = k1_relat_1(sK3)) )),
% 1.43/0.58    inference(forward_demodulation,[],[f251,f112])).
% 1.43/0.58  fof(f251,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK6(sK0,sK3),X0),sK3) | sK0 = k1_relset_1(sK0,sK1,sK3)) )),
% 1.43/0.58    inference(resolution,[],[f58,f50])).
% 1.43/0.58  fof(f138,plain,(
% 1.43/0.58    ( ! [X2,X3] : (r2_hidden(sK7(X2,X3,sK3),k1_relat_1(sK3)) | ~r2_hidden(X2,k9_relat_1(sK3,X3))) )),
% 1.43/0.58    inference(resolution,[],[f135,f109])).
% 1.43/0.58  fof(f109,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f108,f90])).
% 1.43/0.58  fof(f108,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.43/0.58    inference(resolution,[],[f54,f48])).
% 1.43/0.58  fof(f54,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f32])).
% 1.43/0.58  % SZS output end Proof for theBenchmark
% 1.43/0.58  % (27543)------------------------------
% 1.43/0.58  % (27543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (27543)Termination reason: Refutation
% 1.43/0.58  
% 1.43/0.58  % (27543)Memory used [KB]: 6780
% 1.43/0.58  % (27543)Time elapsed: 0.168 s
% 1.43/0.58  % (27543)------------------------------
% 1.43/0.58  % (27543)------------------------------
% 1.43/0.58  % (27537)Success in time 0.226 s
%------------------------------------------------------------------------------
