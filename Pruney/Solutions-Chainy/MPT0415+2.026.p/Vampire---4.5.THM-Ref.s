%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:24 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   20
%              Number of atoms          :  231 ( 429 expanded)
%              Number of equality atoms :   58 ( 112 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f119,plain,(
    k1_xboole_0 = sK1 ),
    inference(superposition,[],[f113,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f113,plain,(
    ! [X0] : sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f110,plain,(
    ! [X0] : r1_xboole_0(sK1,X0) ),
    inference(resolution,[],[f109,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f109,plain,(
    ! [X1] : ~ r2_hidden(X1,sK1) ),
    inference(subsumption_resolution,[],[f108,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f108,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f107,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | k1_xboole_0 != k1_xboole_0 ) ),
    inference(superposition,[],[f99,f58])).

fof(f58,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f57,f30])).

fof(f57,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f40,f32])).

fof(f32,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k7_setfam_1(X4,X5),k1_zfmisc_1(k1_zfmisc_1(X4)))
      | ~ r2_hidden(X3,k7_setfam_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
      | k1_xboole_0 != X5 ) ),
    inference(resolution,[],[f97,f69])).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | k1_xboole_0 != X2 ) ),
    inference(condensation,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != X2
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f65,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f49,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) != X0
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

% (28853)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
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
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:21:26 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.44  % (28850)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.44  % (28846)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.47  % (28844)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.47  % (28844)Refutation not found, incomplete strategy% (28844)------------------------------
% 0.18/0.47  % (28844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (28856)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.48  % (28844)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (28844)Memory used [KB]: 1663
% 0.18/0.48  % (28844)Time elapsed: 0.080 s
% 0.18/0.48  % (28844)------------------------------
% 0.18/0.48  % (28844)------------------------------
% 0.18/0.48  % (28868)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.48  % (28847)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.48  % (28864)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.48  % (28847)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f125,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(subsumption_resolution,[],[f119,f31])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    k1_xboole_0 != sK1),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(flattening,[],[f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(ennf_transformation,[],[f11])).
% 0.18/0.49  fof(f11,negated_conjecture,(
% 0.18/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.18/0.49    inference(negated_conjecture,[],[f10])).
% 0.18/0.49  fof(f10,conjecture,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.18/0.49  fof(f119,plain,(
% 0.18/0.49    k1_xboole_0 = sK1),
% 0.18/0.49    inference(superposition,[],[f113,f49])).
% 0.18/0.49  fof(f49,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f35,f36])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.18/0.49  fof(f113,plain,(
% 0.18/0.49    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 0.18/0.49    inference(resolution,[],[f110,f51])).
% 0.18/0.49  fof(f51,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.18/0.49    inference(definition_unfolding,[],[f46,f36])).
% 0.18/0.49  fof(f46,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.49    inference(nnf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.18/0.49  fof(f110,plain,(
% 0.18/0.49    ( ! [X0] : (r1_xboole_0(sK1,X0)) )),
% 0.18/0.49    inference(resolution,[],[f109,f37])).
% 0.18/0.49  fof(f37,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f23])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.49    inference(ennf_transformation,[],[f12])).
% 0.18/0.49  fof(f12,plain,(
% 0.18/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.49    inference(rectify,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.18/0.49  fof(f109,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(X1,sK1)) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f108,f33])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.18/0.49  fof(f108,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f107,f30])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f107,plain,(
% 0.18/0.49    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(X1,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.18/0.49    inference(trivial_inequality_removal,[],[f104])).
% 0.18/0.49  fof(f104,plain,(
% 0.18/0.49    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(X1,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 != k1_xboole_0) )),
% 0.18/0.49    inference(superposition,[],[f99,f58])).
% 0.18/0.49  fof(f58,plain,(
% 0.18/0.49    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.18/0.49    inference(subsumption_resolution,[],[f57,f30])).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.18/0.49    inference(superposition,[],[f40,f32])).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(ennf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.18/0.49  fof(f99,plain,(
% 0.18/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(k7_setfam_1(X4,X5),k1_zfmisc_1(k1_zfmisc_1(X4))) | ~r2_hidden(X3,k7_setfam_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4))) | k1_xboole_0 != X5) )),
% 0.18/0.49    inference(resolution,[],[f97,f69])).
% 0.18/0.49  fof(f69,plain,(
% 0.18/0.49    ( ! [X2,X3] : (~r2_hidden(X3,X2) | k1_xboole_0 != X2) )),
% 0.18/0.49    inference(condensation,[],[f68])).
% 0.18/0.49  fof(f68,plain,(
% 0.18/0.49    ( ! [X4,X2,X3] : (k1_xboole_0 != X2 | ~r2_hidden(X3,X4) | ~r2_hidden(X3,X2)) )),
% 0.18/0.49    inference(resolution,[],[f66,f39])).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f23])).
% 0.18/0.49  fof(f66,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != X0) )),
% 0.18/0.49    inference(forward_demodulation,[],[f65,f54])).
% 0.18/0.49  fof(f54,plain,(
% 0.18/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.18/0.49    inference(superposition,[],[f49,f34])).
% 0.18/0.49  fof(f34,plain,(
% 0.18/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.49  fof(f65,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) != X0 | r1_xboole_0(X0,X1)) )),
% 0.18/0.49    inference(duplicate_literal_removal,[],[f62])).
% 0.18/0.49  fof(f62,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) != X0 | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 0.18/0.49    inference(resolution,[],[f60,f37])).
% 0.18/0.49  fof(f60,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X1,X2)) )),
% 0.18/0.49    inference(resolution,[],[f55,f37])).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | ~r2_hidden(X2,X0)) )),
% 0.18/0.49    inference(resolution,[],[f50,f39])).
% 0.18/0.49  fof(f50,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 0.18/0.49    inference(definition_unfolding,[],[f47,f36])).
% 0.18/0.49  fof(f47,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f29])).
% 0.18/0.49  % (28853)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.49  fof(f97,plain,(
% 0.18/0.49    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f53,f48])).
% 0.18/0.49  fof(f48,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.18/0.49    inference(flattening,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.18/0.49    inference(ennf_transformation,[],[f9])).
% 0.18/0.49  fof(f9,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.18/0.49  fof(f53,plain,(
% 0.18/0.49    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.18/0.49    inference(equality_resolution,[],[f41])).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(rectify,[],[f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(flattening,[],[f24])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(nnf_transformation,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.18/0.49    inference(ennf_transformation,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (28847)------------------------------
% 0.18/0.49  % (28847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (28847)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (28847)Memory used [KB]: 10746
% 0.18/0.49  % (28847)Time elapsed: 0.078 s
% 0.18/0.49  % (28847)------------------------------
% 0.18/0.49  % (28847)------------------------------
% 0.18/0.49  % (28862)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.49  % (28862)Refutation not found, incomplete strategy% (28862)------------------------------
% 0.18/0.49  % (28862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (28862)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (28862)Memory used [KB]: 10618
% 0.18/0.49  % (28862)Time elapsed: 0.106 s
% 0.18/0.49  % (28862)------------------------------
% 0.18/0.49  % (28862)------------------------------
% 0.18/0.49  % (28843)Success in time 0.158 s
%------------------------------------------------------------------------------
