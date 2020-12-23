%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:21 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 190 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  213 ( 565 expanded)
%              Number of equality atoms :   38 ( 233 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(resolution,[],[f149,f48])).

fof(f48,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f31])).

fof(f31,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f149,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f147,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f147,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f146,f79])).

fof(f79,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(forward_demodulation,[],[f78,f58])).

fof(f58,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f57,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f78,plain,(
    ~ v1_xboole_0(k7_setfam_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,
    ( ~ v1_xboole_0(k7_setfam_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ v1_xboole_0(k7_setfam_1(sK0,X1))
      | sK1 = X1 ) ),
    inference(superposition,[],[f59,f39])).

fof(f59,plain,(
    ! [X0] :
      ( sK1 = k7_setfam_1(sK0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f58,f36])).

fof(f74,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f70,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f40,f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f142,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f142,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[],[f134,f58])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_setfam_1(sK0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f133,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_setfam_1(sK0,X1))
      | m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f69,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f74,f36])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ r2_hidden(X3,k7_setfam_1(X2,X1)) ) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_setfam_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_setfam_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X0),X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f52,f77])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1) ) ),
    inference(subsumption_resolution,[],[f50,f40])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | r2_hidden(sK3(X0,X1,X2),X2) )
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (21791)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (21807)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (21800)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (21804)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.34/0.52  % (21794)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.34/0.53  % (21796)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.34/0.53  % (21795)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.34/0.53  % (21792)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.53  % (21807)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f150,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(resolution,[],[f149,f48])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    v1_xboole_0(sK4)),
% 1.34/0.53    inference(cnf_transformation,[],[f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    v1_xboole_0(sK4)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ? [X0] : v1_xboole_0(X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 1.34/0.53  fof(f149,plain,(
% 1.34/0.53    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f148])).
% 1.34/0.53  fof(f148,plain,(
% 1.34/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(superposition,[],[f147,f36])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.34/0.53  fof(f147,plain,(
% 1.34/0.53    ~v1_xboole_0(k1_xboole_0)),
% 1.34/0.53    inference(subsumption_resolution,[],[f146,f79])).
% 1.34/0.53  fof(f79,plain,(
% 1.34/0.53    ~v1_xboole_0(sK1)),
% 1.34/0.53    inference(forward_demodulation,[],[f78,f58])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 1.34/0.53    inference(subsumption_resolution,[],[f57,f33])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(flattening,[],[f11])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(ennf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.34/0.53    inference(negated_conjecture,[],[f9])).
% 1.34/0.53  fof(f9,conjecture,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.34/0.53    inference(superposition,[],[f39,f35])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.34/0.53  fof(f78,plain,(
% 1.34/0.53    ~v1_xboole_0(k7_setfam_1(sK0,k1_xboole_0))),
% 1.34/0.53    inference(subsumption_resolution,[],[f75,f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    k1_xboole_0 != sK1),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    ~v1_xboole_0(k7_setfam_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.34/0.53    inference(resolution,[],[f74,f62])).
% 1.34/0.53  fof(f62,plain,(
% 1.34/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v1_xboole_0(k7_setfam_1(sK0,X1)) | sK1 = X1) )),
% 1.34/0.53    inference(superposition,[],[f59,f39])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    ( ! [X0] : (sK1 = k7_setfam_1(sK0,X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(superposition,[],[f58,f36])).
% 1.34/0.53  fof(f74,plain,(
% 1.34/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.34/0.53    inference(subsumption_resolution,[],[f70,f33])).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.34/0.53    inference(superposition,[],[f40,f35])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(ennf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.34/0.53  fof(f146,plain,(
% 1.34/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK1)),
% 1.34/0.53    inference(resolution,[],[f142,f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.53    inference(rectify,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.53    inference(nnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.53  fof(f142,plain,(
% 1.34/0.53    ( ! [X1] : (~r2_hidden(X1,sK1) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.34/0.53    inference(superposition,[],[f134,f58])).
% 1.34/0.53  fof(f134,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k7_setfam_1(sK0,X1)) | ~v1_xboole_0(X1)) )),
% 1.34/0.53    inference(subsumption_resolution,[],[f133,f105])).
% 1.34/0.53  fof(f105,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k7_setfam_1(sK0,X1)) | m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_xboole_0(X1)) )),
% 1.34/0.53    inference(resolution,[],[f69,f77])).
% 1.34/0.53  fof(f77,plain,(
% 1.34/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(superposition,[],[f74,f36])).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) | m1_subset_1(X3,k1_zfmisc_1(X2)) | ~r2_hidden(X3,k7_setfam_1(X2,X1))) )),
% 1.34/0.53    inference(resolution,[],[f40,f47])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.34/0.53  fof(f133,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k7_setfam_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_xboole_0(X1)) )),
% 1.34/0.53    inference(subsumption_resolution,[],[f129,f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f129,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k7_setfam_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X0),X1) | ~v1_xboole_0(X1)) )),
% 1.34/0.53    inference(resolution,[],[f52,f77])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X4,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X4),X1)) )),
% 1.34/0.53    inference(subsumption_resolution,[],[f50,f40])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.34/0.53    inference(equality_resolution,[],[f41])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(rectify,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(flattening,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(nnf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.34/0.53    inference(ennf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (21807)------------------------------
% 1.34/0.53  % (21807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (21807)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (21807)Memory used [KB]: 1663
% 1.34/0.53  % (21807)Time elapsed: 0.090 s
% 1.34/0.53  % (21807)------------------------------
% 1.34/0.53  % (21807)------------------------------
% 1.34/0.53  % (21793)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.34/0.53  % (21788)Success in time 0.174 s
%------------------------------------------------------------------------------
