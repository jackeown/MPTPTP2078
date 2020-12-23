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
% DateTime   : Thu Dec  3 13:23:24 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 204 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   21
%              Number of atoms          :  304 (1238 expanded)
%              Number of equality atoms :   49 ( 172 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(subsumption_resolution,[],[f434,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f434,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f433,f43])).

fof(f43,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f433,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f406,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f406,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f403,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f403,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f368,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f45,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f123,f46])).

fof(f46,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f122,f47])).

fof(f47,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f368,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(resolution,[],[f354,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f354,plain,(
    ~ r1_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    inference(resolution,[],[f350,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f65,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f350,plain,(
    ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f347])).

fof(f347,plain,
    ( sK1 != sK1
    | ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f210,f156])).

fof(f156,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X5) = X4
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(forward_demodulation,[],[f149,f121])).

fof(f121,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f116,f52])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f116,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f62,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f90,f61])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f82,f52])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f63,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f149,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X5) = k5_xboole_0(X4,k1_xboole_0)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f62,f75])).

fof(f75,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X2,X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f65,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f210,plain,(
    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f209,f42])).

fof(f209,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f43])).

fof(f208,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f44])).

fof(f207,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f46])).

fof(f206,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f47])).

fof(f205,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f48])).

fof(f201,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f49,f134])).

fof(f134,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k1_tarski(k1_xboole_0)) = k2_yellow19(X2,k3_yellow19(X2,k2_struct_0(X2),X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
      | v1_xboole_0(X3)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k1_tarski(k1_xboole_0)) = k2_yellow19(X2,k3_yellow19(X2,k2_struct_0(X2),X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X2)))
      | v1_xboole_0(X3)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2))))) ) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f49,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (819265538)
% 0.14/0.36  ipcrm: permission denied for id (818216963)
% 0.14/0.36  ipcrm: permission denied for id (819298308)
% 0.14/0.36  ipcrm: permission denied for id (819331077)
% 0.14/0.37  ipcrm: permission denied for id (819363846)
% 0.14/0.37  ipcrm: permission denied for id (819396615)
% 0.14/0.37  ipcrm: permission denied for id (818282505)
% 0.14/0.37  ipcrm: permission denied for id (819593230)
% 0.14/0.38  ipcrm: permission denied for id (819625999)
% 0.14/0.38  ipcrm: permission denied for id (819658768)
% 0.14/0.38  ipcrm: permission denied for id (819691537)
% 0.14/0.38  ipcrm: permission denied for id (819822613)
% 0.14/0.39  ipcrm: permission denied for id (819888151)
% 0.14/0.39  ipcrm: permission denied for id (819986458)
% 0.14/0.39  ipcrm: permission denied for id (820019227)
% 0.20/0.39  ipcrm: permission denied for id (820051996)
% 0.20/0.39  ipcrm: permission denied for id (820084765)
% 0.20/0.39  ipcrm: permission denied for id (818380830)
% 0.20/0.39  ipcrm: permission denied for id (820117535)
% 0.20/0.40  ipcrm: permission denied for id (818413600)
% 0.20/0.40  ipcrm: permission denied for id (818446373)
% 0.20/0.40  ipcrm: permission denied for id (820314151)
% 0.20/0.40  ipcrm: permission denied for id (820346920)
% 0.20/0.41  ipcrm: permission denied for id (820412458)
% 0.20/0.41  ipcrm: permission denied for id (820445227)
% 0.20/0.41  ipcrm: permission denied for id (820477996)
% 0.20/0.41  ipcrm: permission denied for id (820510765)
% 0.20/0.41  ipcrm: permission denied for id (820543534)
% 0.20/0.41  ipcrm: permission denied for id (820576303)
% 0.20/0.41  ipcrm: permission denied for id (820609072)
% 0.20/0.41  ipcrm: permission denied for id (820641841)
% 0.20/0.41  ipcrm: permission denied for id (820674610)
% 0.20/0.42  ipcrm: permission denied for id (820707379)
% 0.20/0.42  ipcrm: permission denied for id (820772917)
% 0.20/0.42  ipcrm: permission denied for id (820805686)
% 0.20/0.42  ipcrm: permission denied for id (818577463)
% 0.20/0.42  ipcrm: permission denied for id (818610232)
% 0.20/0.42  ipcrm: permission denied for id (820871226)
% 0.20/0.42  ipcrm: permission denied for id (820936763)
% 0.20/0.43  ipcrm: permission denied for id (820969532)
% 0.20/0.43  ipcrm: permission denied for id (821035070)
% 0.20/0.43  ipcrm: permission denied for id (821166146)
% 0.20/0.44  ipcrm: permission denied for id (821362760)
% 0.20/0.44  ipcrm: permission denied for id (821428298)
% 0.20/0.44  ipcrm: permission denied for id (821493836)
% 0.20/0.45  ipcrm: permission denied for id (821559374)
% 0.20/0.45  ipcrm: permission denied for id (821624912)
% 0.20/0.45  ipcrm: permission denied for id (818708561)
% 0.20/0.45  ipcrm: permission denied for id (818741330)
% 0.20/0.45  ipcrm: permission denied for id (821657683)
% 0.20/0.45  ipcrm: permission denied for id (821723221)
% 0.20/0.46  ipcrm: permission denied for id (821854297)
% 0.20/0.46  ipcrm: permission denied for id (821887066)
% 0.20/0.46  ipcrm: permission denied for id (821919835)
% 0.20/0.46  ipcrm: permission denied for id (821952604)
% 0.20/0.46  ipcrm: permission denied for id (821985373)
% 0.20/0.47  ipcrm: permission denied for id (822050911)
% 0.20/0.47  ipcrm: permission denied for id (822083680)
% 0.20/0.47  ipcrm: permission denied for id (818905186)
% 0.20/0.47  ipcrm: permission denied for id (822181988)
% 0.20/0.47  ipcrm: permission denied for id (822214757)
% 0.20/0.47  ipcrm: permission denied for id (818937958)
% 0.20/0.48  ipcrm: permission denied for id (822280296)
% 0.20/0.48  ipcrm: permission denied for id (822313065)
% 0.20/0.48  ipcrm: permission denied for id (822378603)
% 0.20/0.48  ipcrm: permission denied for id (822411372)
% 0.20/0.48  ipcrm: permission denied for id (822542448)
% 0.20/0.49  ipcrm: permission denied for id (822607986)
% 0.20/0.49  ipcrm: permission denied for id (822640755)
% 0.20/0.49  ipcrm: permission denied for id (822706293)
% 0.20/0.49  ipcrm: permission denied for id (819101815)
% 0.20/0.49  ipcrm: permission denied for id (819134585)
% 0.20/0.50  ipcrm: permission denied for id (819167356)
% 0.35/0.57  % (31284)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.35/0.60  % (31272)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.35/0.60  % (31283)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.35/0.61  % (31271)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.35/0.61  % (31278)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.35/0.61  % (31282)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.35/0.61  % (31273)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.35/0.62  % (31279)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.35/0.62  % (31276)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.35/0.62  % (31275)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.35/0.62  % (31277)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.35/0.62  % (31287)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.35/0.63  % (31286)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.35/0.63  % (31280)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.35/0.63  % (31281)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.35/0.63  % (31270)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.35/0.63  % (31273)Refutation found. Thanks to Tanya!
% 0.35/0.63  % SZS status Theorem for theBenchmark
% 0.35/0.63  % SZS output start Proof for theBenchmark
% 0.35/0.63  fof(f435,plain,(
% 0.35/0.63    $false),
% 0.35/0.63    inference(subsumption_resolution,[],[f434,f42])).
% 0.35/0.63  fof(f42,plain,(
% 0.35/0.63    ~v2_struct_0(sK0)),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f33,plain,(
% 0.35/0.63    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.35/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f32,f31])).
% 0.35/0.63  fof(f31,plain,(
% 0.35/0.63    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.35/0.63    introduced(choice_axiom,[])).
% 0.35/0.63  fof(f32,plain,(
% 0.35/0.63    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.35/0.63    introduced(choice_axiom,[])).
% 0.35/0.63  fof(f20,plain,(
% 0.35/0.63    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.35/0.63    inference(flattening,[],[f19])).
% 0.35/0.63  fof(f19,plain,(
% 0.35/0.63    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.35/0.63    inference(ennf_transformation,[],[f17])).
% 0.35/0.63  fof(f17,negated_conjecture,(
% 0.35/0.63    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.35/0.63    inference(negated_conjecture,[],[f16])).
% 0.35/0.63  fof(f16,conjecture,(
% 0.35/0.63    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.35/0.63  fof(f434,plain,(
% 0.35/0.63    v2_struct_0(sK0)),
% 0.35/0.63    inference(subsumption_resolution,[],[f433,f43])).
% 0.35/0.63  fof(f43,plain,(
% 0.35/0.63    l1_struct_0(sK0)),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f433,plain,(
% 0.35/0.63    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.35/0.63    inference(resolution,[],[f406,f55])).
% 0.35/0.63  fof(f55,plain,(
% 0.35/0.63    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f24])).
% 0.35/0.63  fof(f24,plain,(
% 0.35/0.63    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.35/0.63    inference(flattening,[],[f23])).
% 0.35/0.63  fof(f23,plain,(
% 0.35/0.63    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.35/0.63    inference(ennf_transformation,[],[f12])).
% 0.35/0.63  fof(f12,axiom,(
% 0.35/0.63    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.35/0.63  fof(f406,plain,(
% 0.35/0.63    v1_xboole_0(k2_struct_0(sK0))),
% 0.35/0.63    inference(subsumption_resolution,[],[f403,f50])).
% 0.35/0.63  fof(f50,plain,(
% 0.35/0.63    v1_xboole_0(k1_xboole_0)),
% 0.35/0.63    inference(cnf_transformation,[],[f3])).
% 0.35/0.63  fof(f3,axiom,(
% 0.35/0.63    v1_xboole_0(k1_xboole_0)),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.35/0.63  fof(f403,plain,(
% 0.35/0.63    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_struct_0(sK0))),
% 0.35/0.63    inference(resolution,[],[f368,f126])).
% 0.35/0.63  fof(f126,plain,(
% 0.35/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.35/0.63    inference(subsumption_resolution,[],[f125,f44])).
% 0.35/0.63  fof(f44,plain,(
% 0.35/0.63    ~v1_xboole_0(sK1)),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f125,plain,(
% 0.35/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.35/0.63    inference(subsumption_resolution,[],[f124,f45])).
% 0.35/0.63  fof(f45,plain,(
% 0.35/0.63    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f124,plain,(
% 0.35/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.35/0.63    inference(subsumption_resolution,[],[f123,f46])).
% 0.35/0.63  fof(f46,plain,(
% 0.35/0.63    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f123,plain,(
% 0.35/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.35/0.63    inference(subsumption_resolution,[],[f122,f47])).
% 0.35/0.63  fof(f47,plain,(
% 0.35/0.63    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f122,plain,(
% 0.35/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.35/0.63    inference(resolution,[],[f54,f48])).
% 0.35/0.63  fof(f48,plain,(
% 0.35/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.35/0.63    inference(cnf_transformation,[],[f33])).
% 0.35/0.63  fof(f54,plain,(
% 0.35/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f22])).
% 0.35/0.63  fof(f22,plain,(
% 0.35/0.63    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.35/0.63    inference(flattening,[],[f21])).
% 0.35/0.63  fof(f21,plain,(
% 0.35/0.63    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.35/0.63    inference(ennf_transformation,[],[f15])).
% 0.35/0.63  fof(f15,axiom,(
% 0.35/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.35/0.63  fof(f368,plain,(
% 0.35/0.63    r2_hidden(k1_xboole_0,sK1)),
% 0.35/0.63    inference(resolution,[],[f354,f66])).
% 0.35/0.63  fof(f66,plain,(
% 0.35/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f29])).
% 0.35/0.63  fof(f29,plain,(
% 0.35/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.35/0.63    inference(ennf_transformation,[],[f9])).
% 0.35/0.63  fof(f9,axiom,(
% 0.35/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.35/0.63  fof(f354,plain,(
% 0.35/0.63    ~r1_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 0.35/0.63    inference(resolution,[],[f350,f160])).
% 0.35/0.63  fof(f160,plain,(
% 0.35/0.63    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.35/0.63    inference(resolution,[],[f76,f64])).
% 0.35/0.63  fof(f64,plain,(
% 0.35/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f41])).
% 0.35/0.63  fof(f41,plain,(
% 0.35/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.35/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f40])).
% 0.35/0.63  fof(f40,plain,(
% 0.35/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.35/0.63    introduced(choice_axiom,[])).
% 0.35/0.63  fof(f28,plain,(
% 0.35/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.35/0.63    inference(ennf_transformation,[],[f18])).
% 0.35/0.63  fof(f18,plain,(
% 0.35/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.35/0.63    inference(rectify,[],[f4])).
% 0.35/0.63  fof(f4,axiom,(
% 0.35/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.35/0.63  fof(f76,plain,(
% 0.35/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.35/0.63    inference(superposition,[],[f65,f61])).
% 0.35/0.63  fof(f61,plain,(
% 0.35/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f1])).
% 0.35/0.63  fof(f1,axiom,(
% 0.35/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.35/0.63  fof(f65,plain,(
% 0.35/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f41])).
% 0.35/0.63  fof(f350,plain,(
% 0.35/0.63    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.35/0.63    inference(trivial_inequality_removal,[],[f347])).
% 0.35/0.63  fof(f347,plain,(
% 0.35/0.63    sK1 != sK1 | ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.35/0.63    inference(superposition,[],[f210,f156])).
% 0.35/0.63  fof(f156,plain,(
% 0.35/0.63    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = X4 | ~r1_xboole_0(X4,X5)) )),
% 0.35/0.63    inference(forward_demodulation,[],[f149,f121])).
% 0.35/0.63  fof(f121,plain,(
% 0.35/0.63    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.35/0.63    inference(forward_demodulation,[],[f116,f52])).
% 0.35/0.63  fof(f52,plain,(
% 0.35/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.35/0.63    inference(cnf_transformation,[],[f6])).
% 0.35/0.63  fof(f6,axiom,(
% 0.35/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.35/0.63  fof(f116,plain,(
% 0.35/0.63    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.35/0.63    inference(superposition,[],[f62,f93])).
% 0.35/0.63  fof(f93,plain,(
% 0.35/0.63    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.35/0.63    inference(superposition,[],[f90,f61])).
% 0.35/0.63  fof(f90,plain,(
% 0.35/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.35/0.63    inference(forward_demodulation,[],[f82,f52])).
% 0.35/0.63  fof(f82,plain,(
% 0.35/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.35/0.63    inference(superposition,[],[f63,f51])).
% 0.35/0.63  fof(f51,plain,(
% 0.35/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.35/0.63    inference(cnf_transformation,[],[f8])).
% 0.35/0.63  fof(f8,axiom,(
% 0.35/0.63    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.35/0.63  fof(f63,plain,(
% 0.35/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.35/0.63    inference(cnf_transformation,[],[f7])).
% 0.35/0.63  fof(f7,axiom,(
% 0.35/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.35/0.63  fof(f62,plain,(
% 0.35/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.35/0.63    inference(cnf_transformation,[],[f5])).
% 0.35/0.63  fof(f5,axiom,(
% 0.35/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.35/0.63  fof(f149,plain,(
% 0.35/0.63    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,k1_xboole_0) | ~r1_xboole_0(X4,X5)) )),
% 0.35/0.63    inference(superposition,[],[f62,f75])).
% 0.35/0.63  fof(f75,plain,(
% 0.35/0.63    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,X3) | ~r1_xboole_0(X2,X3)) )),
% 0.35/0.63    inference(resolution,[],[f65,f59])).
% 0.35/0.63  fof(f59,plain,(
% 0.35/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.35/0.63    inference(cnf_transformation,[],[f39])).
% 0.35/0.63  fof(f39,plain,(
% 0.35/0.63    ! [X0] : ((r1_xboole_0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.35/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f38])).
% 0.35/0.63  fof(f38,plain,(
% 0.35/0.63    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.35/0.63    introduced(choice_axiom,[])).
% 0.35/0.63  fof(f27,plain,(
% 0.35/0.63    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.35/0.63    inference(ennf_transformation,[],[f11])).
% 0.35/0.63  fof(f11,axiom,(
% 0.35/0.63    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.35/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.35/0.63  fof(f210,plain,(
% 0.35/0.63    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.35/0.64    inference(subsumption_resolution,[],[f209,f42])).
% 0.35/0.64  fof(f209,plain,(
% 0.35/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | v2_struct_0(sK0)),
% 0.35/0.64    inference(subsumption_resolution,[],[f208,f43])).
% 0.35/0.64  fof(f208,plain,(
% 0.35/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.35/0.64    inference(subsumption_resolution,[],[f207,f44])).
% 0.35/0.64  fof(f207,plain,(
% 0.35/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.35/0.64    inference(subsumption_resolution,[],[f206,f46])).
% 0.35/0.64  fof(f206,plain,(
% 0.35/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.35/0.64    inference(subsumption_resolution,[],[f205,f47])).
% 0.35/0.64  fof(f205,plain,(
% 0.35/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.35/0.64    inference(subsumption_resolution,[],[f201,f48])).
% 0.35/0.64  fof(f201,plain,(
% 0.35/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.35/0.64    inference(superposition,[],[f49,f134])).
% 0.35/0.64  fof(f134,plain,(
% 0.35/0.64    ( ! [X2,X3] : (k4_xboole_0(X3,k1_tarski(k1_xboole_0)) = k2_yellow19(X2,k3_yellow19(X2,k2_struct_0(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X2))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X2))) | v1_xboole_0(X3) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.35/0.64    inference(duplicate_literal_removal,[],[f131])).
% 0.35/0.64  fof(f131,plain,(
% 0.35/0.64    ( ! [X2,X3] : (k4_xboole_0(X3,k1_tarski(k1_xboole_0)) = k2_yellow19(X2,k3_yellow19(X2,k2_struct_0(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X2))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X2))) | v1_xboole_0(X3) | ~l1_struct_0(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X2)))))) )),
% 0.35/0.64    inference(superposition,[],[f56,f67])).
% 0.35/0.64  fof(f67,plain,(
% 0.35/0.64    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.35/0.64    inference(cnf_transformation,[],[f30])).
% 0.35/0.64  fof(f30,plain,(
% 0.35/0.64    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.35/0.64    inference(ennf_transformation,[],[f10])).
% 0.35/0.64  fof(f10,axiom,(
% 0.35/0.64    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.35/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.35/0.64  fof(f56,plain,(
% 0.35/0.64    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.35/0.64    inference(cnf_transformation,[],[f26])).
% 0.35/0.64  fof(f26,plain,(
% 0.35/0.64    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.35/0.64    inference(flattening,[],[f25])).
% 0.35/0.64  fof(f25,plain,(
% 0.35/0.64    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.35/0.64    inference(ennf_transformation,[],[f14])).
% 0.35/0.64  fof(f14,axiom,(
% 0.35/0.64    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.35/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 0.35/0.64  fof(f49,plain,(
% 0.35/0.64    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.35/0.64    inference(cnf_transformation,[],[f33])).
% 0.35/0.64  % SZS output end Proof for theBenchmark
% 0.35/0.64  % (31273)------------------------------
% 0.35/0.64  % (31273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.35/0.64  % (31273)Termination reason: Refutation
% 0.35/0.64  
% 0.35/0.64  % (31273)Memory used [KB]: 1791
% 0.35/0.64  % (31273)Time elapsed: 0.068 s
% 0.35/0.64  % (31273)------------------------------
% 0.35/0.64  % (31273)------------------------------
% 0.35/0.64  % (31135)Success in time 0.285 s
%------------------------------------------------------------------------------
