%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0365+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:50 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   88 (1612 expanded)
%              Number of leaves         :   10 ( 442 expanded)
%              Depth                    :   24
%              Number of atoms          :  299 (9933 expanded)
%              Number of equality atoms :   63 (1676 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f855,plain,(
    $false ),
    inference(subsumption_resolution,[],[f854,f29])).

fof(f29,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
        & r1_xboole_0(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(f854,plain,(
    sK1 = k3_subset_1(sK0,sK2) ),
    inference(backward_demodulation,[],[f656,f853])).

fof(f853,plain,(
    sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f852,f838])).

fof(f838,plain,(
    r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1) ),
    inference(subsumption_resolution,[],[f837,f29])).

fof(f837,plain,
    ( sK1 = k3_subset_1(sK0,sK2)
    | r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1) ),
    inference(forward_demodulation,[],[f835,f656])).

fof(f835,plain,
    ( sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f832])).

fof(f832,plain,
    ( sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1)
    | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1) ),
    inference(resolution,[],[f678,f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(X2,k3_subset_1(sK0,sK1),X3),sK0)
      | r2_hidden(sK4(X2,k3_subset_1(sK0,sK1),X3),sK1)
      | k4_xboole_0(X2,k3_subset_1(sK0,sK1)) = X3
      | r2_hidden(sK4(X2,k3_subset_1(sK0,sK1),X3),X3) ) ),
    inference(resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f80,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f42,f47])).

fof(f47,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f678,plain,(
    ! [X14] :
      ( r2_hidden(sK4(sK1,X14,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X14) ) ),
    inference(duplicate_literal_removal,[],[f673])).

fof(f673,plain,(
    ! [X14] :
      ( r2_hidden(sK4(sK1,X14,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X14)
      | r2_hidden(sK4(sK1,X14,sK1),sK0) ) ),
    inference(resolution,[],[f94,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f44,f67])).

fof(f67,plain,(
    sK1 = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f62,f46])).

fof(f46,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f62,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f34])).

fof(f48,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,sK1),sK0)
      | r2_hidden(sK4(X2,X3,sK1),X2)
      | sK1 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f852,plain,
    ( ~ r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1)
    | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f850,f847])).

fof(f847,plain,(
    ~ r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f158,f838,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f158,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | r1_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f113,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(k3_subset_1(sK0,sK1),X1),sK1)
      | r1_xboole_0(k3_subset_1(sK0,sK1),X1) ) ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f43,f47])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f850,plain,
    ( r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),k3_subset_1(sK0,sK1))
    | ~ r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),sK1),sK1)
    | sK1 = k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f838,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f656,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f644,f390])).

fof(f390,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0,k3_subset_1(sK0,sK2)),sK1)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X0) ) ),
    inference(factoring,[],[f162])).

fof(f162,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(X1,X2,k3_subset_1(sK0,sK2)),sK1)
      | r2_hidden(sK4(X1,X2,k3_subset_1(sK0,sK2)),X1)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(X1,X2) ) ),
    inference(subsumption_resolution,[],[f161,f118])).

fof(f118,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,k3_subset_1(sK0,sK2)),sK0)
      | r2_hidden(sK4(X2,X3,k3_subset_1(sK0,sK2)),X2)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f82,f39])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK2))
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f44,f52])).

fof(f52,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f26,f34])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f161,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(X1,X2,k3_subset_1(sK0,sK2)),X1)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(X1,X2)
      | r2_hidden(sK4(X1,X2,k3_subset_1(sK0,sK2)),sK1)
      | ~ r2_hidden(sK4(X1,X2,k3_subset_1(sK0,sK2)),sK0) ) ),
    inference(resolution,[],[f90,f80])).

fof(f90,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(X2,X3,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1))
      | r2_hidden(sK4(X2,X3,k3_subset_1(sK0,sK2)),X2)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK2))
      | ~ r2_hidden(X0,k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f28,f32])).

fof(f28,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f644,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ r2_hidden(sK4(sK1,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f625,f79])).

fof(f625,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),X9)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X9) ) ),
    inference(subsumption_resolution,[],[f624,f390])).

fof(f624,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),X9)
      | ~ r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),sK1)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X9) ) ),
    inference(subsumption_resolution,[],[f619,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f27,f32])).

fof(f27,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f619,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),sK2)
      | r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),X9)
      | ~ r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),sK1)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X9) ) ),
    inference(duplicate_literal_removal,[],[f616])).

fof(f616,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),sK2)
      | r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),X9)
      | ~ r2_hidden(sK4(sK1,X9,k3_subset_1(sK0,sK2)),sK1)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X9)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X9) ) ),
    inference(resolution,[],[f128,f295])).

fof(f295,plain,(
    ! [X15] :
      ( r2_hidden(sK4(sK1,X15,k3_subset_1(sK0,sK2)),sK0)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X15) ) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,(
    ! [X15] :
      ( r2_hidden(sK4(sK1,X15,k3_subset_1(sK0,sK2)),sK0)
      | k3_subset_1(sK0,sK2) = k4_xboole_0(sK1,X15)
      | r2_hidden(sK4(sK1,X15,k3_subset_1(sK0,sK2)),sK0) ) ),
    inference(resolution,[],[f118,f85])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,k3_subset_1(sK0,sK2)),sK0)
      | r2_hidden(sK4(X0,X1,k3_subset_1(sK0,sK2)),sK2)
      | r2_hidden(sK4(X0,X1,k3_subset_1(sK0,sK2)),X1)
      | ~ r2_hidden(sK4(X0,X1,k3_subset_1(sK0,sK2)),X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(sK0,sK2) ) ),
    inference(resolution,[],[f84,f41])).

fof(f84,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK2))
      | r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f42,f52])).

%------------------------------------------------------------------------------
