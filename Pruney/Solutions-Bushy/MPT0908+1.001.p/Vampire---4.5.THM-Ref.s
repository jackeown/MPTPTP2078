%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0908+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 123 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  230 ( 720 expanded)
%              Number of equality atoms :  170 ( 598 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(global_subsumption,[],[f17,f61,f68,f77])).

fof(f77,plain,(
    sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f76,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
       => ~ ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f74,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f73,f19])).

fof(f19,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | sK5 = k6_mcart_1(X0,X1,X2,sK3) ) ),
    inference(superposition,[],[f56,f18])).

fof(f18,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X6 ) ),
    inference(subsumption_resolution,[],[f38,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f38,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)),X1)
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X6 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X1)
      | X4 = X6
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) != X4 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X1)
      | k3_mcart_1(X5,X6,X7) != X3
      | X4 = X6
      | k6_mcart_1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k6_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X6
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( k6_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X6 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).

fof(f68,plain,(
    sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f66,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f65,f21])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f64,f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | sK6 = k7_mcart_1(X0,X1,X2,sK3) ) ),
    inference(superposition,[],[f55,f18])).

fof(f55,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X7 ) ),
    inference(subsumption_resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f40,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)),X2)
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X7 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X2)
      | X4 = X7
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) != X4 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X2)
      | k3_mcart_1(X5,X6,X7) != X3
      | X4 = X7
      | k7_mcart_1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X7
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ( k7_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X7 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_mcart_1)).

fof(f61,plain,(
    sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f60,f20])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f59,f22])).

fof(f59,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f57,f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | sK4 = k5_mcart_1(X0,X1,X2,sK3) ) ),
    inference(superposition,[],[f54,f18])).

fof(f54,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X5 ) ),
    inference(subsumption_resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f36,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)),X0)
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X5 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X0)
      | X4 = X5
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) != X4 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X0)
      | k3_mcart_1(X5,X6,X7) != X3
      | X4 = X5
      | k5_mcart_1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_mcart_1)).

fof(f17,plain,
    ( sK4 != k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
