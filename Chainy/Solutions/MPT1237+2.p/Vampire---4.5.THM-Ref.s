%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1237+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 5.19s
% Output     : Refutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 467 expanded)
%              Number of leaves         :   12 ( 171 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 (2078 expanded)
%              Number of equality atoms :   23 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8282,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8262,f4610])).

fof(f4610,plain,(
    ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f4609,f4585])).

fof(f4585,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f2594,f2398])).

fof(f2398,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2200])).

fof(f2200,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2594,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2319,f2321,f2325])).

fof(f2325,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2139])).

fof(f2139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2138])).

fof(f2138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f2321,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2244])).

fof(f2244,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2135,f2243,f2242,f2241])).

fof(f2241,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2242,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2243,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2135,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2134])).

fof(f2134,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2117])).

fof(f2117,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2116])).

fof(f2116,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f2319,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2244])).

fof(f4609,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f4579,f3997])).

fof(f3997,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2513,f2398])).

fof(f2513,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2319,f2320,f2325])).

fof(f2320,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2244])).

fof(f4579,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2513,f2323,f2594,f2381])).

fof(f2381,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2273])).

fof(f2273,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f2183])).

fof(f2183,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f505])).

fof(f505,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f2323,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f2244])).

fof(f8262,plain,(
    r1_tarski(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f8148,f8223])).

fof(f8223,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f8222,f4585])).

fof(f8222,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f8199,f6090])).

fof(f6090,plain,(
    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2319,f2655,f2363])).

fof(f2363,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2164])).

fof(f2164,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2163])).

fof(f2163,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2655,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f2635,f2634])).

fof(f2634,plain,(
    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f2321,f2398])).

fof(f2635,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2321,f2399])).

fof(f2399,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2201])).

fof(f2201,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f8199,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f2397,f2685])).

fof(f2685,plain,(
    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))) ),
    inference(forward_demodulation,[],[f2595,f2634])).

fof(f2595,plain,(
    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(unit_resulting_resolution,[],[f2319,f2321,f2326])).

fof(f2326,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2140])).

fof(f2140,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2086])).

fof(f2086,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f2397,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2199])).

fof(f2199,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f8148,plain,(
    r1_tarski(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f6733,f8115])).

fof(f8115,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f8114,f3997])).

fof(f8114,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f8091,f5802])).

fof(f5802,plain,(
    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2319,f2567,f2363])).

fof(f2567,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f2547,f2546])).

fof(f2546,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f2320,f2398])).

fof(f2547,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2320,f2399])).

fof(f8091,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f2397,f2588])).

fof(f2588,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f2514,f2546])).

fof(f2514,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f2319,f2320,f2326])).

fof(f6733,plain,(
    r1_tarski(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f2319,f2655,f2567,f2658,f2366])).

fof(f2366,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2170])).

fof(f2170,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2169])).

fof(f2169,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1840])).

fof(f1840,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f2658,plain,(
    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f2657,f2634])).

fof(f2657,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f2627,f2546])).

fof(f2627,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f2322,f2320,f2321,f2380])).

fof(f2380,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2273])).

fof(f2322,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f2244])).
%------------------------------------------------------------------------------
