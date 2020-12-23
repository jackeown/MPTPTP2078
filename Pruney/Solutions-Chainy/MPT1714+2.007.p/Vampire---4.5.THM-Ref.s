%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 552 expanded)
%              Number of leaves         :    8 ( 100 expanded)
%              Depth                    :   25
%              Number of atoms          :  214 (3531 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(global_subsumption,[],[f26,f176,f180])).

fof(f180,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f179,f96])).

fof(f96,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f82,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f78,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f30,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f179,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f178,f61])).

fof(f61,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f54,f40])).

fof(f54,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f50,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f27,f39])).

fof(f27,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f178,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f176,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f176,plain,(
    r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f175,f96])).

fof(f175,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f173,f61])).

fof(f173,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f170,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f170,plain,(
    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(superposition,[],[f154,f112])).

fof(f112,plain,(
    u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f108,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f108,plain,(
    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f107,f61])).

fof(f107,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f105,f77])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f70,f40])).

fof(f70,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f29,f39])).

fof(f29,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3) ),
    inference(resolution,[],[f102,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f101,f77])).

fof(f101,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f98,f61])).

fof(f98,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(resolution,[],[f95,f33])).

fof(f95,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f94,f61])).

fof(f94,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f91,f77])).

fof(f91,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f25,f33])).

fof(f25,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f154,plain,(
    ! [X0] : r1_xboole_0(u1_struct_0(sK1),k4_xboole_0(X0,u1_struct_0(sK2))) ),
    inference(resolution,[],[f152,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f152,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f151,f28])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f151,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f86,f29])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK1,X0)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK1,X0)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK1,X0)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f26,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7670)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (7677)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (7672)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (7672)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(global_subsumption,[],[f26,f176,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    r1_tsep_1(sK3,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f82,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.20/0.50    inference(resolution,[],[f30,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    l1_struct_0(sK3)),
% 0.20/0.50    inference(resolution,[],[f54,f40])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    l1_pre_topc(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f50,f32])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.20/0.50    inference(resolution,[],[f27,f39])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    m1_pre_topc(sK3,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 0.20/0.50    inference(resolution,[],[f176,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    r1_tsep_1(sK1,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f175,f96])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f173,f61])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3)),
% 0.20/0.50    inference(resolution,[],[f170,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.20/0.50    inference(superposition,[],[f154,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.50    inference(resolution,[],[f108,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f61])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    l1_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f70,f40])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    l1_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f66,f32])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.20/0.50    inference(resolution,[],[f29,f39])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3)),
% 0.20/0.50    inference(resolution,[],[f102,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    r1_tsep_1(sK3,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f77])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f98,f61])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.20/0.50    inference(resolution,[],[f95,f33])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    r1_tsep_1(sK2,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f61])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f91,f77])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.20/0.50    inference(resolution,[],[f25,f33])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(u1_struct_0(sK1),k4_xboole_0(X0,u1_struct_0(sK2)))) )),
% 0.20/0.50    inference(resolution,[],[f152,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f151,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK2) | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.50    inference(resolution,[],[f86,f29])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,X0) | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f85,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,X0) | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f80,f32])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK1,X0) | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0))) )),
% 0.20/0.50    inference(resolution,[],[f30,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (7672)------------------------------
% 0.20/0.50  % (7672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7672)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (7672)Memory used [KB]: 6140
% 0.20/0.50  % (7672)Time elapsed: 0.089 s
% 0.20/0.50  % (7672)------------------------------
% 0.20/0.50  % (7672)------------------------------
% 0.20/0.50  % (7664)Success in time 0.141 s
%------------------------------------------------------------------------------
