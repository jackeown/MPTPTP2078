%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:26 EST 2020

% Result     : Theorem 17.64s
% Output     : Refutation 17.64s
% Verified   : 
% Statistics : Number of formulae       :  148 (1515 expanded)
%              Number of leaves         :   28 ( 444 expanded)
%              Depth                    :   22
%              Number of atoms          :  525 (3866 expanded)
%              Number of equality atoms :  208 (1561 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11841,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11832,f6075])).

fof(f6075,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f6054])).

fof(f6054,plain,
    ( sK0 != sK0
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(superposition,[],[f1629,f6018])).

fof(f6018,plain,(
    sK0 = sK8(sK0,sK0,sK0,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1942,f4815])).

fof(f4815,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f4792])).

fof(f4792,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(resolution,[],[f982,f173])).

fof(f173,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f129,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f121,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f126,f141])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f137,f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f138,f139])).

fof(f139,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f138,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f126,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f121,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f129,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK8(X0,X1,X2,X3) != X2
              & sK8(X0,X1,X2,X3) != X1
              & sK8(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sK8(X0,X1,X2,X3) = X2
            | sK8(X0,X1,X2,X3) = X1
            | sK8(X0,X1,X2,X3) = X0
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f77,f78])).

fof(f78,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK8(X0,X1,X2,X3) != X2
            & sK8(X0,X1,X2,X3) != X1
            & sK8(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sK8(X0,X1,X2,X3) = X2
          | sK8(X0,X1,X2,X3) = X1
          | sK8(X0,X1,X2,X3) = X0
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f982,plain,(
    ! [X0] :
      ( r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f341,f112])).

fof(f112,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f341,plain,(
    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f335,f198])).

fof(f198,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f147,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f147,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f82,f145])).

fof(f145,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f87,f144])).

fof(f144,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f99,f143])).

fof(f99,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f87,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f56])).

fof(f56,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f335,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f196,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f196,plain,(
    v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f147,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1942,plain,
    ( sK0 = sK8(sK0,sK0,sK0,k1_relat_1(sK3))
    | r2_hidden(sK8(sK0,sK0,sK0,k1_relat_1(sK3)),k1_relat_1(sK3)) ),
    inference(equality_resolution,[],[f1941])).

fof(f1941,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) != X0
      | sK0 = sK8(sK0,sK0,sK0,X0)
      | r2_hidden(sK8(sK0,sK0,sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f557,f945])).

fof(f945,plain,(
    ! [X2] : r1_tarski(k9_relat_1(sK3,X2),k2_relat_1(sK3)) ),
    inference(resolution,[],[f943,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f943,plain,(
    ! [X1] : m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(forward_demodulation,[],[f317,f316])).

fof(f316,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0) ),
    inference(resolution,[],[f301,f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f301,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f175,f198])).

fof(f175,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f317,plain,(
    ! [X1] : m1_subset_1(k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X1),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(resolution,[],[f301,f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f557,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) != X0
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
      | sK0 = sK8(sK0,sK0,sK0,X0)
      | r2_hidden(sK8(sK0,sK0,sK0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f553])).

fof(f553,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) != X0
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
      | sK0 = sK8(sK0,sK0,sK0,X0)
      | sK0 = sK8(sK0,sK0,sK0,X0)
      | sK0 = sK8(sK0,sK0,sK0,X0)
      | r2_hidden(sK8(sK0,sK0,sK0,X0),X0) ) ),
    inference(superposition,[],[f534,f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK8(X0,X1,X2,X3) = X2
      | sK8(X0,X1,X2,X3) = X1
      | sK8(X0,X1,X2,X3) = X0
      | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f133,f143])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK8(X0,X1,X2,X3) = X2
      | sK8(X0,X1,X2,X3) = X1
      | sK8(X0,X1,X2,X3) = X0
      | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f534,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f533,f198])).

fof(f533,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f527,f80])).

fof(f527,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f509,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f108,f145,f145])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f509,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f146,f194])).

fof(f194,plain,(
    ! [X0] : k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f147,f128])).

fof(f146,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f84,f145,f145])).

fof(f84,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f1629,plain,(
    ! [X1] :
      ( sK0 != sK8(sK0,sK0,sK0,X1)
      | k1_relat_1(sK3) != X1
      | ~ r2_hidden(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f558,f945])).

fof(f558,plain,(
    ! [X1] :
      ( k1_relat_1(sK3) != X1
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
      | sK0 != sK8(sK0,sK0,sK0,X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(inner_rewriting,[],[f554])).

fof(f554,plain,(
    ! [X1] :
      ( k1_relat_1(sK3) != X1
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
      | sK0 != sK8(sK0,sK0,sK0,X1)
      | ~ r2_hidden(sK8(sK0,sK0,sK0,X1),X1) ) ),
    inference(superposition,[],[f534,f153])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK8(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f134,f143])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK8(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f11832,plain,(
    r2_hidden(sK0,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f7316,f11660])).

fof(f11660,plain,(
    sK0 = sK7(k1_relat_1(sK3),k1_xboole_0) ),
    inference(resolution,[],[f7316,f4815])).

fof(f7316,plain,(
    r2_hidden(sK7(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3)) ),
    inference(resolution,[],[f6885,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f6885,plain,(
    ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f6881,f198])).

fof(f6881,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f6853,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f6853,plain,(
    ~ v4_relat_1(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f6828,f945])).

fof(f6828,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(resolution,[],[f4579,f645])).

fof(f645,plain,(
    ! [X1] :
      ( r2_hidden(sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),X1)
      | ~ r1_tarski(k9_relat_1(sK3,sK2),X1) ) ),
    inference(resolution,[],[f525,f112])).

fof(f525,plain,(
    r2_hidden(sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k9_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f509,f113])).

fof(f4579,plain,(
    ! [X15] :
      ( ~ r2_hidden(X15,k2_relat_1(sK3))
      | ~ v4_relat_1(sK3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f4518,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f4518,plain,(
    ! [X15] :
      ( ~ r1_tarski(k1_xboole_0,sK6(sK3,X15))
      | ~ r2_hidden(X15,k2_relat_1(sK3))
      | ~ v4_relat_1(sK3,k1_xboole_0) ) ),
    inference(superposition,[],[f383,f3594])).

fof(f3594,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_xboole_0) ),
    inference(resolution,[],[f746,f85])).

fof(f746,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_relat_1(sK3))
      | k1_relat_1(sK3) = X5
      | ~ v4_relat_1(sK3,X5) ) ),
    inference(resolution,[],[f242,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f242,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(sK3),X7)
      | ~ v4_relat_1(sK3,X7) ) ),
    inference(resolution,[],[f198,f102])).

fof(f383,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(sK3),sK6(sK3,X5))
      | ~ r2_hidden(X5,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f379,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f379,plain,(
    ! [X10] :
      ( r2_hidden(sK6(sK3,X10),k1_relat_1(sK3))
      | ~ r2_hidden(X10,k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f185,f198])).

fof(f185,plain,(
    ! [X10] :
      ( r2_hidden(sK6(sK3,X10),k1_relat_1(sK3))
      | ~ r2_hidden(X10,k2_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f80,f162])).

fof(f162,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f59,f62,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (18483)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (18501)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (18493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (18492)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (18485)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (18484)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (18504)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (18482)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (18480)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (18480)Refutation not found, incomplete strategy% (18480)------------------------------
% 0.22/0.54  % (18480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18480)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18480)Memory used [KB]: 10874
% 0.22/0.54  % (18480)Time elapsed: 0.123 s
% 0.22/0.54  % (18480)------------------------------
% 0.22/0.54  % (18480)------------------------------
% 0.22/0.54  % (18488)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (18478)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (18506)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (18479)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (18505)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (18496)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18491)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (18502)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (18494)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (18495)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (18497)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18507)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (18500)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (18498)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (18486)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (18490)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (18487)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (18481)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (18503)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (18499)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (18489)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.98/0.68  % (18513)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.28/0.84  % (18483)Time limit reached!
% 3.28/0.84  % (18483)------------------------------
% 3.28/0.84  % (18483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.84  % (18483)Termination reason: Time limit
% 3.28/0.84  
% 3.28/0.84  % (18483)Memory used [KB]: 8955
% 3.28/0.84  % (18483)Time elapsed: 0.427 s
% 3.28/0.84  % (18483)------------------------------
% 3.28/0.84  % (18483)------------------------------
% 4.19/0.92  % (18490)Time limit reached!
% 4.19/0.92  % (18490)------------------------------
% 4.19/0.92  % (18490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.92  % (18490)Termination reason: Time limit
% 4.19/0.92  
% 4.19/0.92  % (18490)Memory used [KB]: 8315
% 4.19/0.92  % (18490)Time elapsed: 0.510 s
% 4.19/0.92  % (18490)------------------------------
% 4.19/0.92  % (18490)------------------------------
% 4.39/0.93  % (18488)Time limit reached!
% 4.39/0.93  % (18488)------------------------------
% 4.39/0.93  % (18488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (18488)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (18488)Memory used [KB]: 18293
% 4.39/0.93  % (18488)Time elapsed: 0.519 s
% 4.39/0.93  % (18488)------------------------------
% 4.39/0.93  % (18488)------------------------------
% 4.39/0.93  % (18479)Time limit reached!
% 4.39/0.93  % (18479)------------------------------
% 4.39/0.93  % (18479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (18479)Termination reason: Time limit
% 4.39/0.93  % (18479)Termination phase: Saturation
% 4.39/0.93  
% 4.39/0.93  % (18479)Memory used [KB]: 8187
% 4.39/0.93  % (18479)Time elapsed: 0.500 s
% 4.39/0.93  % (18479)------------------------------
% 4.39/0.93  % (18479)------------------------------
% 4.39/0.93  % (18478)Time limit reached!
% 4.39/0.93  % (18478)------------------------------
% 4.39/0.93  % (18478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (18478)Termination reason: Time limit
% 4.39/0.93  % (18478)Termination phase: Saturation
% 4.39/0.93  
% 4.39/0.93  % (18478)Memory used [KB]: 3837
% 4.39/0.93  % (18478)Time elapsed: 0.500 s
% 4.39/0.93  % (18478)------------------------------
% 4.39/0.93  % (18478)------------------------------
% 4.39/0.93  % (18495)Time limit reached!
% 4.39/0.93  % (18495)------------------------------
% 4.39/0.93  % (18495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (18495)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (18495)Memory used [KB]: 15095
% 4.39/0.93  % (18495)Time elapsed: 0.515 s
% 4.39/0.93  % (18495)------------------------------
% 4.39/0.93  % (18495)------------------------------
% 4.39/0.98  % (18520)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.39/1.01  % (18506)Time limit reached!
% 4.39/1.01  % (18506)------------------------------
% 4.39/1.01  % (18506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/1.01  % (18506)Termination reason: Time limit
% 4.39/1.01  % (18506)Termination phase: Saturation
% 4.39/1.01  
% 4.39/1.01  % (18506)Memory used [KB]: 7419
% 4.39/1.01  % (18506)Time elapsed: 0.600 s
% 4.39/1.01  % (18506)------------------------------
% 4.39/1.01  % (18506)------------------------------
% 5.04/1.02  % (18494)Time limit reached!
% 5.04/1.02  % (18494)------------------------------
% 5.04/1.02  % (18494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.02  % (18494)Termination reason: Time limit
% 5.04/1.02  
% 5.04/1.02  % (18494)Memory used [KB]: 14583
% 5.04/1.02  % (18494)Time elapsed: 0.605 s
% 5.04/1.02  % (18494)------------------------------
% 5.04/1.02  % (18494)------------------------------
% 5.04/1.04  % (18522)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.04/1.06  % (18521)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.04/1.06  % (18524)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.04/1.07  % (18485)Time limit reached!
% 5.04/1.07  % (18485)------------------------------
% 5.04/1.07  % (18485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.07  % (18485)Termination reason: Time limit
% 5.04/1.07  % (18485)Termination phase: Saturation
% 5.04/1.07  
% 5.04/1.07  % (18485)Memory used [KB]: 11257
% 5.04/1.07  % (18485)Time elapsed: 0.600 s
% 5.04/1.07  % (18485)------------------------------
% 5.04/1.07  % (18485)------------------------------
% 5.04/1.07  % (18523)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.04/1.07  % (18525)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.51/1.15  % (18526)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.51/1.17  % (18527)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.39/1.19  % (18528)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.78/1.23  % (18499)Time limit reached!
% 6.78/1.23  % (18499)------------------------------
% 6.78/1.23  % (18499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.78/1.23  % (18499)Termination reason: Time limit
% 6.78/1.23  % (18499)Termination phase: Saturation
% 6.78/1.23  
% 6.78/1.23  % (18499)Memory used [KB]: 4349
% 6.78/1.23  % (18499)Time elapsed: 0.800 s
% 6.78/1.23  % (18499)------------------------------
% 6.78/1.23  % (18499)------------------------------
% 7.43/1.37  % (18529)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.43/1.38  % (18523)Time limit reached!
% 7.43/1.38  % (18523)------------------------------
% 7.43/1.38  % (18523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.43/1.38  % (18523)Termination reason: Time limit
% 7.43/1.38  
% 7.43/1.38  % (18523)Memory used [KB]: 13176
% 7.43/1.38  % (18523)Time elapsed: 0.421 s
% 7.43/1.38  % (18523)------------------------------
% 7.43/1.38  % (18523)------------------------------
% 8.00/1.39  % (18522)Time limit reached!
% 8.00/1.39  % (18522)------------------------------
% 8.00/1.39  % (18522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.00/1.39  % (18522)Termination reason: Time limit
% 8.00/1.39  
% 8.00/1.39  % (18522)Memory used [KB]: 8443
% 8.00/1.39  % (18522)Time elapsed: 0.406 s
% 8.00/1.39  % (18522)------------------------------
% 8.00/1.39  % (18522)------------------------------
% 8.81/1.51  % (18530)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.12/1.54  % (18531)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.70/1.62  % (18500)Time limit reached!
% 9.70/1.62  % (18500)------------------------------
% 9.70/1.62  % (18500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.70/1.62  % (18500)Termination reason: Time limit
% 9.70/1.62  
% 9.70/1.62  % (18500)Memory used [KB]: 15863
% 9.70/1.62  % (18500)Time elapsed: 1.208 s
% 9.70/1.62  % (18500)------------------------------
% 9.70/1.62  % (18500)------------------------------
% 10.50/1.74  % (18504)Time limit reached!
% 10.50/1.74  % (18504)------------------------------
% 10.50/1.74  % (18504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.74  % (18504)Termination reason: Time limit
% 10.50/1.74  
% 10.50/1.74  % (18504)Memory used [KB]: 24562
% 10.50/1.74  % (18504)Time elapsed: 1.304 s
% 10.50/1.74  % (18504)------------------------------
% 10.50/1.74  % (18504)------------------------------
% 10.50/1.77  % (18493)Time limit reached!
% 10.50/1.77  % (18493)------------------------------
% 10.50/1.77  % (18493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.77  % (18493)Termination reason: Time limit
% 10.50/1.77  
% 10.50/1.77  % (18493)Memory used [KB]: 16502
% 10.50/1.77  % (18493)Time elapsed: 1.312 s
% 10.50/1.77  % (18493)------------------------------
% 10.50/1.77  % (18493)------------------------------
% 11.22/1.78  % (18532)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.22/1.79  % (18502)Time limit reached!
% 11.22/1.79  % (18502)------------------------------
% 11.22/1.79  % (18502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.22/1.79  % (18502)Termination reason: Time limit
% 11.22/1.79  
% 11.22/1.79  % (18502)Memory used [KB]: 26993
% 11.22/1.79  % (18502)Time elapsed: 1.338 s
% 11.22/1.79  % (18502)------------------------------
% 11.22/1.79  % (18502)------------------------------
% 11.49/1.88  % (18533)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.49/1.91  % (18505)Time limit reached!
% 11.49/1.91  % (18505)------------------------------
% 11.49/1.91  % (18505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.49/1.91  % (18505)Termination reason: Time limit
% 11.49/1.91  % (18505)Termination phase: Saturation
% 11.49/1.91  
% 11.49/1.91  % (18505)Memory used [KB]: 12537
% 11.49/1.91  % (18505)Time elapsed: 1.500 s
% 11.49/1.91  % (18505)------------------------------
% 11.49/1.91  % (18505)------------------------------
% 11.49/1.91  % (18534)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 12.20/1.93  % (18535)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.20/1.93  % (18531)Time limit reached!
% 12.20/1.93  % (18531)------------------------------
% 12.20/1.93  % (18531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.20/1.93  % (18531)Termination reason: Time limit
% 12.20/1.93  % (18531)Termination phase: Saturation
% 12.20/1.93  
% 12.20/1.93  % (18531)Memory used [KB]: 2430
% 12.20/1.93  % (18531)Time elapsed: 0.500 s
% 12.20/1.93  % (18531)------------------------------
% 12.20/1.93  % (18531)------------------------------
% 12.20/1.99  % (18482)Time limit reached!
% 12.20/1.99  % (18482)------------------------------
% 12.20/1.99  % (18482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.20/1.99  % (18482)Termination reason: Time limit
% 12.20/1.99  
% 12.20/1.99  % (18482)Memory used [KB]: 22259
% 12.20/1.99  % (18482)Time elapsed: 1.539 s
% 12.20/1.99  % (18482)------------------------------
% 12.20/1.99  % (18482)------------------------------
% 12.79/2.03  % (18489)Time limit reached!
% 12.79/2.03  % (18489)------------------------------
% 12.79/2.03  % (18489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.79/2.03  % (18489)Termination reason: Time limit
% 12.79/2.03  % (18489)Termination phase: Saturation
% 12.79/2.03  
% 12.79/2.03  % (18489)Memory used [KB]: 19829
% 12.79/2.03  % (18489)Time elapsed: 1.600 s
% 12.79/2.03  % (18489)------------------------------
% 12.79/2.03  % (18489)------------------------------
% 12.79/2.05  % (18536)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.79/2.07  % (18537)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.29/2.13  % (18538)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.29/2.15  % (18539)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.91/2.19  % (18525)Time limit reached!
% 13.91/2.19  % (18525)------------------------------
% 13.91/2.19  % (18525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.91/2.19  % (18525)Termination reason: Time limit
% 13.91/2.19  % (18525)Termination phase: Saturation
% 13.91/2.19  
% 13.91/2.19  % (18525)Memory used [KB]: 12025
% 13.91/2.19  % (18525)Time elapsed: 1.200 s
% 13.91/2.19  % (18525)------------------------------
% 13.91/2.19  % (18525)------------------------------
% 14.16/2.25  % (18535)Time limit reached!
% 14.16/2.25  % (18535)------------------------------
% 14.16/2.25  % (18535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.16/2.25  % (18535)Termination reason: Time limit
% 14.16/2.25  
% 14.16/2.25  % (18535)Memory used [KB]: 4989
% 14.16/2.25  % (18535)Time elapsed: 0.422 s
% 14.16/2.25  % (18535)------------------------------
% 14.16/2.25  % (18535)------------------------------
% 14.87/2.32  % (18540)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 14.87/2.37  % (18492)Time limit reached!
% 14.87/2.37  % (18492)------------------------------
% 14.87/2.37  % (18492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.87/2.37  % (18492)Termination reason: Time limit
% 14.87/2.37  
% 14.87/2.37  % (18492)Memory used [KB]: 6396
% 14.87/2.37  % (18492)Time elapsed: 1.957 s
% 14.87/2.37  % (18492)------------------------------
% 14.87/2.37  % (18492)------------------------------
% 14.87/2.37  % (18541)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.19/2.42  % (18538)Time limit reached!
% 16.19/2.42  % (18538)------------------------------
% 16.19/2.42  % (18538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.19/2.42  % (18538)Termination reason: Time limit
% 16.19/2.42  % (18538)Termination phase: Saturation
% 16.19/2.42  
% 16.19/2.42  % (18538)Memory used [KB]: 2686
% 16.19/2.42  % (18538)Time elapsed: 0.400 s
% 16.19/2.42  % (18538)------------------------------
% 16.19/2.42  % (18538)------------------------------
% 16.19/2.42  % (18496)Time limit reached!
% 16.19/2.42  % (18496)------------------------------
% 16.19/2.42  % (18496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.19/2.42  % (18496)Termination reason: Time limit
% 16.19/2.42  
% 16.19/2.42  % (18496)Memory used [KB]: 13816
% 16.19/2.42  % (18496)Time elapsed: 2.010 s
% 16.19/2.42  % (18496)------------------------------
% 16.19/2.42  % (18496)------------------------------
% 16.19/2.45  % (18484)Time limit reached!
% 16.19/2.45  % (18484)------------------------------
% 16.19/2.45  % (18484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.19/2.45  % (18484)Termination reason: Time limit
% 16.19/2.45  
% 16.19/2.45  % (18484)Memory used [KB]: 19957
% 16.19/2.45  % (18484)Time elapsed: 2.021 s
% 16.19/2.45  % (18484)------------------------------
% 16.19/2.45  % (18484)------------------------------
% 16.84/2.53  % (18542)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.84/2.58  % (18544)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.84/2.58  % (18543)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.55/2.59  % (18545)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.64/2.60  % (18530)Refutation found. Thanks to Tanya!
% 17.64/2.60  % SZS status Theorem for theBenchmark
% 17.64/2.60  % SZS output start Proof for theBenchmark
% 17.64/2.60  fof(f11841,plain,(
% 17.64/2.60    $false),
% 17.64/2.60    inference(subsumption_resolution,[],[f11832,f6075])).
% 17.64/2.60  fof(f6075,plain,(
% 17.64/2.60    ~r2_hidden(sK0,k1_relat_1(sK3))),
% 17.64/2.60    inference(trivial_inequality_removal,[],[f6054])).
% 17.64/2.60  fof(f6054,plain,(
% 17.64/2.60    sK0 != sK0 | k1_relat_1(sK3) != k1_relat_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3))),
% 17.64/2.60    inference(superposition,[],[f1629,f6018])).
% 17.64/2.60  fof(f6018,plain,(
% 17.64/2.60    sK0 = sK8(sK0,sK0,sK0,k1_relat_1(sK3))),
% 17.64/2.60    inference(subsumption_resolution,[],[f1942,f4815])).
% 17.64/2.60  fof(f4815,plain,(
% 17.64/2.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK0 = X0) )),
% 17.64/2.60    inference(duplicate_literal_removal,[],[f4792])).
% 17.64/2.60  fof(f4792,plain,(
% 17.64/2.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK0 = X0 | sK0 = X0 | sK0 = X0) )),
% 17.64/2.60    inference(resolution,[],[f982,f173])).
% 17.64/2.60  fof(f173,plain,(
% 17.64/2.60    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 17.64/2.60    inference(equality_resolution,[],[f158])).
% 17.64/2.60  fof(f158,plain,(
% 17.64/2.60    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 17.64/2.60    inference(definition_unfolding,[],[f129,f143])).
% 17.64/2.60  fof(f143,plain,(
% 17.64/2.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f121,f142])).
% 17.64/2.60  fof(f142,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f126,f141])).
% 17.64/2.60  fof(f141,plain,(
% 17.64/2.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f137,f140])).
% 17.64/2.60  fof(f140,plain,(
% 17.64/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f138,f139])).
% 17.64/2.60  fof(f139,plain,(
% 17.64/2.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f11])).
% 17.64/2.60  fof(f11,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 17.64/2.60  fof(f138,plain,(
% 17.64/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f10])).
% 17.64/2.60  fof(f10,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 17.64/2.60  fof(f137,plain,(
% 17.64/2.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f9])).
% 17.64/2.60  fof(f9,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 17.64/2.60  fof(f126,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f8])).
% 17.64/2.60  fof(f8,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 17.64/2.60  fof(f121,plain,(
% 17.64/2.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f7])).
% 17.64/2.60  fof(f7,axiom,(
% 17.64/2.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 17.64/2.60  fof(f129,plain,(
% 17.64/2.60    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 17.64/2.60    inference(cnf_transformation,[],[f79])).
% 17.64/2.60  fof(f79,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK8(X0,X1,X2,X3) != X2 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X2 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X0 | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 17.64/2.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f77,f78])).
% 17.64/2.60  fof(f78,plain,(
% 17.64/2.60    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK8(X0,X1,X2,X3) != X2 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X2 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X0 | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 17.64/2.60    introduced(choice_axiom,[])).
% 17.64/2.60  fof(f77,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 17.64/2.60    inference(rectify,[],[f76])).
% 17.64/2.60  fof(f76,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 17.64/2.60    inference(flattening,[],[f75])).
% 17.64/2.60  fof(f75,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 17.64/2.60    inference(nnf_transformation,[],[f55])).
% 17.64/2.60  fof(f55,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 17.64/2.60    inference(ennf_transformation,[],[f4])).
% 17.64/2.60  fof(f4,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 17.64/2.60  fof(f982,plain,(
% 17.64/2.60    ( ! [X0] : (r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 17.64/2.60    inference(resolution,[],[f341,f112])).
% 17.64/2.60  fof(f112,plain,(
% 17.64/2.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f71])).
% 17.64/2.60  fof(f71,plain,(
% 17.64/2.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 17.64/2.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).
% 17.64/2.60  fof(f70,plain,(
% 17.64/2.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 17.64/2.60    introduced(choice_axiom,[])).
% 17.64/2.60  fof(f69,plain,(
% 17.64/2.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 17.64/2.60    inference(rectify,[],[f68])).
% 17.64/2.60  fof(f68,plain,(
% 17.64/2.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 17.64/2.60    inference(nnf_transformation,[],[f47])).
% 17.64/2.60  fof(f47,plain,(
% 17.64/2.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 17.64/2.60    inference(ennf_transformation,[],[f1])).
% 17.64/2.60  fof(f1,axiom,(
% 17.64/2.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 17.64/2.60  fof(f341,plain,(
% 17.64/2.60    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 17.64/2.60    inference(subsumption_resolution,[],[f335,f198])).
% 17.64/2.60  fof(f198,plain,(
% 17.64/2.60    v1_relat_1(sK3)),
% 17.64/2.60    inference(resolution,[],[f147,f122])).
% 17.64/2.60  fof(f122,plain,(
% 17.64/2.60    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 17.64/2.60    inference(cnf_transformation,[],[f49])).
% 17.64/2.60  fof(f49,plain,(
% 17.64/2.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.64/2.60    inference(ennf_transformation,[],[f24])).
% 17.64/2.60  fof(f24,axiom,(
% 17.64/2.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 17.64/2.60  fof(f147,plain,(
% 17.64/2.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 17.64/2.60    inference(definition_unfolding,[],[f82,f145])).
% 17.64/2.60  fof(f145,plain,(
% 17.64/2.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f87,f144])).
% 17.64/2.60  fof(f144,plain,(
% 17.64/2.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f99,f143])).
% 17.64/2.60  fof(f99,plain,(
% 17.64/2.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f6])).
% 17.64/2.60  fof(f6,axiom,(
% 17.64/2.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 17.64/2.60  fof(f87,plain,(
% 17.64/2.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f5])).
% 17.64/2.60  fof(f5,axiom,(
% 17.64/2.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 17.64/2.60  fof(f82,plain,(
% 17.64/2.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 17.64/2.60    inference(cnf_transformation,[],[f57])).
% 17.64/2.60  fof(f57,plain,(
% 17.64/2.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 17.64/2.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f56])).
% 17.64/2.60  fof(f56,plain,(
% 17.64/2.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 17.64/2.60    introduced(choice_axiom,[])).
% 17.64/2.60  fof(f33,plain,(
% 17.64/2.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 17.64/2.60    inference(flattening,[],[f32])).
% 17.64/2.60  fof(f32,plain,(
% 17.64/2.60    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 17.64/2.60    inference(ennf_transformation,[],[f31])).
% 17.64/2.60  fof(f31,negated_conjecture,(
% 17.64/2.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 17.64/2.60    inference(negated_conjecture,[],[f30])).
% 17.64/2.60  fof(f30,conjecture,(
% 17.64/2.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 17.64/2.60  fof(f335,plain,(
% 17.64/2.60    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 17.64/2.60    inference(resolution,[],[f196,f102])).
% 17.64/2.60  fof(f102,plain,(
% 17.64/2.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f65])).
% 17.64/2.60  fof(f65,plain,(
% 17.64/2.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 17.64/2.60    inference(nnf_transformation,[],[f41])).
% 17.64/2.60  fof(f41,plain,(
% 17.64/2.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 17.64/2.60    inference(ennf_transformation,[],[f17])).
% 17.64/2.60  fof(f17,axiom,(
% 17.64/2.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 17.64/2.60  fof(f196,plain,(
% 17.64/2.60    v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 17.64/2.60    inference(resolution,[],[f147,f123])).
% 17.64/2.60  fof(f123,plain,(
% 17.64/2.60    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 17.64/2.60    inference(cnf_transformation,[],[f50])).
% 17.64/2.60  fof(f50,plain,(
% 17.64/2.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.64/2.60    inference(ennf_transformation,[],[f25])).
% 17.64/2.60  fof(f25,axiom,(
% 17.64/2.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 17.64/2.60  fof(f1942,plain,(
% 17.64/2.60    sK0 = sK8(sK0,sK0,sK0,k1_relat_1(sK3)) | r2_hidden(sK8(sK0,sK0,sK0,k1_relat_1(sK3)),k1_relat_1(sK3))),
% 17.64/2.60    inference(equality_resolution,[],[f1941])).
% 17.64/2.60  fof(f1941,plain,(
% 17.64/2.60    ( ! [X0] : (k1_relat_1(sK3) != X0 | sK0 = sK8(sK0,sK0,sK0,X0) | r2_hidden(sK8(sK0,sK0,sK0,X0),X0)) )),
% 17.64/2.60    inference(subsumption_resolution,[],[f557,f945])).
% 17.64/2.60  fof(f945,plain,(
% 17.64/2.60    ( ! [X2] : (r1_tarski(k9_relat_1(sK3,X2),k2_relat_1(sK3))) )),
% 17.64/2.60    inference(resolution,[],[f943,f115])).
% 17.64/2.60  fof(f115,plain,(
% 17.64/2.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 17.64/2.60    inference(cnf_transformation,[],[f72])).
% 17.64/2.60  fof(f72,plain,(
% 17.64/2.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 17.64/2.60    inference(nnf_transformation,[],[f15])).
% 17.64/2.60  fof(f15,axiom,(
% 17.64/2.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 17.64/2.60  fof(f943,plain,(
% 17.64/2.60    ( ! [X1] : (m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(k2_relat_1(sK3)))) )),
% 17.64/2.60    inference(forward_demodulation,[],[f317,f316])).
% 17.64/2.60  fof(f316,plain,(
% 17.64/2.60    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0)) )),
% 17.64/2.60    inference(resolution,[],[f301,f128])).
% 17.64/2.60  fof(f128,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 17.64/2.60    inference(cnf_transformation,[],[f54])).
% 17.64/2.60  fof(f54,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.64/2.60    inference(ennf_transformation,[],[f27])).
% 17.64/2.60  fof(f27,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 17.64/2.60  fof(f301,plain,(
% 17.64/2.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 17.64/2.60    inference(subsumption_resolution,[],[f175,f198])).
% 17.64/2.60  fof(f175,plain,(
% 17.64/2.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 17.64/2.60    inference(resolution,[],[f80,f90])).
% 17.64/2.60  fof(f90,plain,(
% 17.64/2.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f35])).
% 17.64/2.60  fof(f35,plain,(
% 17.64/2.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.64/2.60    inference(flattening,[],[f34])).
% 17.64/2.60  fof(f34,plain,(
% 17.64/2.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.64/2.60    inference(ennf_transformation,[],[f28])).
% 17.64/2.60  fof(f28,axiom,(
% 17.64/2.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 17.64/2.60  fof(f80,plain,(
% 17.64/2.60    v1_funct_1(sK3)),
% 17.64/2.60    inference(cnf_transformation,[],[f57])).
% 17.64/2.60  fof(f317,plain,(
% 17.64/2.60    ( ! [X1] : (m1_subset_1(k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X1),k1_zfmisc_1(k2_relat_1(sK3)))) )),
% 17.64/2.60    inference(resolution,[],[f301,f127])).
% 17.64/2.60  fof(f127,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 17.64/2.60    inference(cnf_transformation,[],[f53])).
% 17.64/2.60  fof(f53,plain,(
% 17.64/2.60    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 17.64/2.60    inference(ennf_transformation,[],[f26])).
% 17.64/2.60  fof(f26,axiom,(
% 17.64/2.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 17.64/2.60  fof(f557,plain,(
% 17.64/2.60    ( ! [X0] : (k1_relat_1(sK3) != X0 | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 = sK8(sK0,sK0,sK0,X0) | r2_hidden(sK8(sK0,sK0,sK0,X0),X0)) )),
% 17.64/2.60    inference(duplicate_literal_removal,[],[f553])).
% 17.64/2.60  fof(f553,plain,(
% 17.64/2.60    ( ! [X0] : (k1_relat_1(sK3) != X0 | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 = sK8(sK0,sK0,sK0,X0) | sK0 = sK8(sK0,sK0,sK0,X0) | sK0 = sK8(sK0,sK0,sK0,X0) | r2_hidden(sK8(sK0,sK0,sK0,X0),X0)) )),
% 17.64/2.60    inference(superposition,[],[f534,f154])).
% 17.64/2.60  fof(f154,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK8(X0,X1,X2,X3) = X2 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X0 | r2_hidden(sK8(X0,X1,X2,X3),X3)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f133,f143])).
% 17.64/2.60  fof(f133,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK8(X0,X1,X2,X3) = X2 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X0 | r2_hidden(sK8(X0,X1,X2,X3),X3)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f79])).
% 17.64/2.60  fof(f534,plain,(
% 17.64/2.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 17.64/2.60    inference(subsumption_resolution,[],[f533,f198])).
% 17.64/2.60  fof(f533,plain,(
% 17.64/2.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 17.64/2.60    inference(subsumption_resolution,[],[f527,f80])).
% 17.64/2.60  fof(f527,plain,(
% 17.64/2.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 17.64/2.60    inference(superposition,[],[f509,f150])).
% 17.64/2.60  fof(f150,plain,(
% 17.64/2.60    ( ! [X0,X1] : (k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f108,f145,f145])).
% 17.64/2.60  fof(f108,plain,(
% 17.64/2.60    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f46])).
% 17.64/2.60  fof(f46,plain,(
% 17.64/2.60    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 17.64/2.60    inference(flattening,[],[f45])).
% 17.64/2.60  fof(f45,plain,(
% 17.64/2.60    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 17.64/2.60    inference(ennf_transformation,[],[f22])).
% 17.64/2.60  fof(f22,axiom,(
% 17.64/2.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 17.64/2.60  fof(f509,plain,(
% 17.64/2.60    ~r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 17.64/2.60    inference(backward_demodulation,[],[f146,f194])).
% 17.64/2.60  fof(f194,plain,(
% 17.64/2.60    ( ! [X0] : (k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 17.64/2.60    inference(resolution,[],[f147,f128])).
% 17.64/2.60  fof(f146,plain,(
% 17.64/2.60    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 17.64/2.60    inference(definition_unfolding,[],[f84,f145,f145])).
% 17.64/2.60  fof(f84,plain,(
% 17.64/2.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 17.64/2.60    inference(cnf_transformation,[],[f57])).
% 17.64/2.60  fof(f1629,plain,(
% 17.64/2.60    ( ! [X1] : (sK0 != sK8(sK0,sK0,sK0,X1) | k1_relat_1(sK3) != X1 | ~r2_hidden(sK0,X1)) )),
% 17.64/2.60    inference(subsumption_resolution,[],[f558,f945])).
% 17.64/2.60  fof(f558,plain,(
% 17.64/2.60    ( ! [X1] : (k1_relat_1(sK3) != X1 | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 != sK8(sK0,sK0,sK0,X1) | ~r2_hidden(sK0,X1)) )),
% 17.64/2.60    inference(inner_rewriting,[],[f554])).
% 17.64/2.60  fof(f554,plain,(
% 17.64/2.60    ( ! [X1] : (k1_relat_1(sK3) != X1 | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | sK0 != sK8(sK0,sK0,sK0,X1) | ~r2_hidden(sK8(sK0,sK0,sK0,X1),X1)) )),
% 17.64/2.60    inference(superposition,[],[f534,f153])).
% 17.64/2.60  fof(f153,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK8(X0,X1,X2,X3) != X0 | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) )),
% 17.64/2.60    inference(definition_unfolding,[],[f134,f143])).
% 17.64/2.60  fof(f134,plain,(
% 17.64/2.60    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK8(X0,X1,X2,X3) != X0 | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f79])).
% 17.64/2.60  fof(f11832,plain,(
% 17.64/2.60    r2_hidden(sK0,k1_relat_1(sK3))),
% 17.64/2.60    inference(backward_demodulation,[],[f7316,f11660])).
% 17.64/2.60  fof(f11660,plain,(
% 17.64/2.60    sK0 = sK7(k1_relat_1(sK3),k1_xboole_0)),
% 17.64/2.60    inference(resolution,[],[f7316,f4815])).
% 17.64/2.60  fof(f7316,plain,(
% 17.64/2.60    r2_hidden(sK7(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3))),
% 17.64/2.60    inference(resolution,[],[f6885,f113])).
% 17.64/2.60  fof(f113,plain,(
% 17.64/2.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f71])).
% 17.64/2.60  fof(f6885,plain,(
% 17.64/2.60    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 17.64/2.60    inference(subsumption_resolution,[],[f6881,f198])).
% 17.64/2.60  fof(f6881,plain,(
% 17.64/2.60    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3)),
% 17.64/2.60    inference(resolution,[],[f6853,f103])).
% 17.64/2.60  fof(f103,plain,(
% 17.64/2.60    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f65])).
% 17.64/2.60  fof(f6853,plain,(
% 17.64/2.60    ~v4_relat_1(sK3,k1_xboole_0)),
% 17.64/2.60    inference(subsumption_resolution,[],[f6828,f945])).
% 17.64/2.60  fof(f6828,plain,(
% 17.64/2.60    ~v4_relat_1(sK3,k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 17.64/2.60    inference(resolution,[],[f4579,f645])).
% 17.64/2.60  fof(f645,plain,(
% 17.64/2.60    ( ! [X1] : (r2_hidden(sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),X1) | ~r1_tarski(k9_relat_1(sK3,sK2),X1)) )),
% 17.64/2.60    inference(resolution,[],[f525,f112])).
% 17.64/2.60  fof(f525,plain,(
% 17.64/2.60    r2_hidden(sK7(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k9_relat_1(sK3,sK2))),
% 17.64/2.60    inference(resolution,[],[f509,f113])).
% 17.64/2.60  fof(f4579,plain,(
% 17.64/2.60    ( ! [X15] : (~r2_hidden(X15,k2_relat_1(sK3)) | ~v4_relat_1(sK3,k1_xboole_0)) )),
% 17.64/2.60    inference(subsumption_resolution,[],[f4518,f85])).
% 17.64/2.60  fof(f85,plain,(
% 17.64/2.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f3])).
% 17.64/2.60  fof(f3,axiom,(
% 17.64/2.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 17.64/2.60  fof(f4518,plain,(
% 17.64/2.60    ( ! [X15] : (~r1_tarski(k1_xboole_0,sK6(sK3,X15)) | ~r2_hidden(X15,k2_relat_1(sK3)) | ~v4_relat_1(sK3,k1_xboole_0)) )),
% 17.64/2.60    inference(superposition,[],[f383,f3594])).
% 17.64/2.60  fof(f3594,plain,(
% 17.64/2.60    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_xboole_0)),
% 17.64/2.60    inference(resolution,[],[f746,f85])).
% 17.64/2.60  fof(f746,plain,(
% 17.64/2.60    ( ! [X5] : (~r1_tarski(X5,k1_relat_1(sK3)) | k1_relat_1(sK3) = X5 | ~v4_relat_1(sK3,X5)) )),
% 17.64/2.60    inference(resolution,[],[f242,f111])).
% 17.64/2.60  fof(f111,plain,(
% 17.64/2.60    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 17.64/2.60    inference(cnf_transformation,[],[f67])).
% 17.64/2.60  fof(f67,plain,(
% 17.64/2.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 17.64/2.60    inference(flattening,[],[f66])).
% 17.64/2.60  fof(f66,plain,(
% 17.64/2.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 17.64/2.60    inference(nnf_transformation,[],[f2])).
% 17.64/2.60  fof(f2,axiom,(
% 17.64/2.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 17.64/2.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 17.64/2.60  fof(f242,plain,(
% 17.64/2.60    ( ! [X7] : (r1_tarski(k1_relat_1(sK3),X7) | ~v4_relat_1(sK3,X7)) )),
% 17.64/2.60    inference(resolution,[],[f198,f102])).
% 17.64/2.60  fof(f383,plain,(
% 17.64/2.61    ( ! [X5] : (~r1_tarski(k1_relat_1(sK3),sK6(sK3,X5)) | ~r2_hidden(X5,k2_relat_1(sK3))) )),
% 17.64/2.61    inference(resolution,[],[f379,f120])).
% 17.64/2.61  fof(f120,plain,(
% 17.64/2.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 17.64/2.61    inference(cnf_transformation,[],[f48])).
% 17.64/2.61  fof(f48,plain,(
% 17.64/2.61    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 17.64/2.61    inference(ennf_transformation,[],[f23])).
% 17.64/2.61  fof(f23,axiom,(
% 17.64/2.61    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 17.64/2.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 17.64/2.61  fof(f379,plain,(
% 17.64/2.61    ( ! [X10] : (r2_hidden(sK6(sK3,X10),k1_relat_1(sK3)) | ~r2_hidden(X10,k2_relat_1(sK3))) )),
% 17.64/2.61    inference(subsumption_resolution,[],[f185,f198])).
% 17.64/2.61  fof(f185,plain,(
% 17.64/2.61    ( ! [X10] : (r2_hidden(sK6(sK3,X10),k1_relat_1(sK3)) | ~r2_hidden(X10,k2_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 17.64/2.61    inference(resolution,[],[f80,f162])).
% 17.64/2.61  fof(f162,plain,(
% 17.64/2.61    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 17.64/2.61    inference(equality_resolution,[],[f92])).
% 17.64/2.61  fof(f92,plain,(
% 17.64/2.61    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 17.64/2.61    inference(cnf_transformation,[],[f63])).
% 17.64/2.61  fof(f63,plain,(
% 17.64/2.61    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.64/2.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f59,f62,f61,f60])).
% 17.64/2.61  fof(f60,plain,(
% 17.64/2.61    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 17.64/2.61    introduced(choice_axiom,[])).
% 17.64/2.61  fof(f61,plain,(
% 17.64/2.61    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 17.64/2.61    introduced(choice_axiom,[])).
% 17.64/2.61  fof(f62,plain,(
% 17.64/2.61    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 17.64/2.61    introduced(choice_axiom,[])).
% 17.64/2.61  fof(f59,plain,(
% 17.64/2.61    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.64/2.61    inference(rectify,[],[f58])).
% 17.64/2.61  fof(f58,plain,(
% 17.64/2.61    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.64/2.61    inference(nnf_transformation,[],[f39])).
% 17.64/2.61  fof(f39,plain,(
% 17.64/2.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 17.64/2.61    inference(flattening,[],[f38])).
% 17.64/2.61  fof(f38,plain,(
% 17.64/2.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 17.64/2.61    inference(ennf_transformation,[],[f21])).
% 17.64/2.61  fof(f21,axiom,(
% 17.64/2.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 17.64/2.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 17.64/2.61  % SZS output end Proof for theBenchmark
% 17.64/2.61  % (18530)------------------------------
% 17.64/2.61  % (18530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.64/2.61  % (18530)Termination reason: Refutation
% 17.64/2.61  
% 17.64/2.61  % (18530)Memory used [KB]: 7419
% 17.64/2.61  % (18530)Time elapsed: 1.196 s
% 17.64/2.61  % (18530)------------------------------
% 17.64/2.61  % (18530)------------------------------
% 17.68/2.61  % (18477)Success in time 2.242 s
%------------------------------------------------------------------------------
