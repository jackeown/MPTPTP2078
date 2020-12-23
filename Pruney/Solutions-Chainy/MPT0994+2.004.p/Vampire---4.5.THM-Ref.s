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
% DateTime   : Thu Dec  3 13:03:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 148 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 ( 854 expanded)
%              Number of equality atoms :   64 ( 232 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f37,f87,f78])).

fof(f78,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,sK5(sK4,X2)),sK4)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f74,f69])).

fof(f69,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK4) ),
    inference(unit_resulting_resolution,[],[f39,f35,f36,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    & k1_xboole_0 != sK1
    & r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK4,sK0,sK1)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
        & k1_xboole_0 != X1
        & r2_hidden(k1_funct_1(X4,X2),X3)
        & r2_hidden(X2,X0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
      & k1_xboole_0 != sK1
      & r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK4,sK0,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

fof(f35,plain,(
    v1_funct_2(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK0 != k1_relset_1(sK0,sK1,sK4)
      | r2_hidden(k4_tarski(X2,sK5(sK4,X2)),sK4) ) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
            & r2_hidden(sK6(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
        & r2_hidden(sK6(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK2,X0),sK4) ),
    inference(unit_resulting_resolution,[],[f70,f85,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f85,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f70,f34,f38,f82,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f82,plain,(
    ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) ),
    inference(unit_resulting_resolution,[],[f70,f34,f77,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f77,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    inference(backward_demodulation,[],[f40,f68])).

fof(f68,plain,(
    ! [X0] : k8_relat_1(X0,sK4) = k6_relset_1(sK0,sK1,X0,sK4) ),
    inference(unit_resulting_resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f40,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f42,f36,f41])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f37,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (6576)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.43  % (6576)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f37,f87,f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X2] : (r2_hidden(k4_tarski(X2,sK5(sK4,X2)),sK4) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f74,f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    sK0 = k1_relset_1(sK0,sK1,sK4)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f39,f35,f36,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(nnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) & k1_xboole_0 != sK1 & r2_hidden(k1_funct_1(sK4,sK2),sK3) & r2_hidden(sK2,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK4,sK0,sK1) & v1_funct_1(sK4)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4] : (k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1 & r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) & k1_xboole_0 != sK1 & r2_hidden(k1_funct_1(sK4,sK2),sK3) & r2_hidden(sK2,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK4,sK0,sK1) & v1_funct_1(sK4))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4] : (k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1 & r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4] : (((k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1) & (r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f9])).
% 0.21/0.43  fof(f9,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    v1_funct_2(sK4,sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    k1_xboole_0 != sK1),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X2] : (~r2_hidden(X2,sK0) | sK0 != k1_relset_1(sK0,sK1,sK4) | r2_hidden(k4_tarski(X2,sK5(sK4,X2)),sK4)) )),
% 0.21/0.43    inference(resolution,[],[f36,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.43    inference(rectify,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.43    inference(nnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(sK2,X0),sK4)) )),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f70,f85,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ~r2_hidden(sK2,k1_relat_1(sK4))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f70,f34,f38,f82,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(nnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f70,f34,f77,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)),
% 0.21/0.43    inference(backward_demodulation,[],[f40,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK4) = k6_relset_1(sK0,sK1,X0,sK4)) )),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f36,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    v1_funct_1(sK4)),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    v1_relat_1(sK4)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f42,f36,f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    r2_hidden(sK2,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (6576)------------------------------
% 0.21/0.43  % (6576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (6576)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (6576)Memory used [KB]: 6140
% 0.21/0.43  % (6576)Time elapsed: 0.034 s
% 0.21/0.43  % (6576)------------------------------
% 0.21/0.43  % (6576)------------------------------
% 0.21/0.44  % (6560)Success in time 0.079 s
%------------------------------------------------------------------------------
