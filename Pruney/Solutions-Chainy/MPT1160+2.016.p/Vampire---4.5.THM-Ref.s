%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  82 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :  238 ( 447 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(resolution,[],[f79,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f79,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f27,f28,f29,f30,f31,f46,f77])).

fof(f77,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0) ),
    inference(resolution,[],[f71,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_orders_2(X0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(k3_orders_2(X0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(k3_orders_2(X0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f61,f39])).

% (24599)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(X0,k3_orders_2(X1,k1_xboole_0,X2)),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,k1_xboole_0,X2)
      | ~ m1_subset_1(k3_orders_2(X1,k1_xboole_0,X2),k1_zfmisc_1(X0))
      | ~ v4_orders_2(X1) ) ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2(X1,k3_orders_2(X0,X2,X3)),u1_struct_0(X0))
      | ~ r1_tarski(X2,sK2(X1,k3_orders_2(X0,X2,X3)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,X2,X3)
      | ~ m1_subset_1(k3_orders_2(X0,X2,X3),k1_zfmisc_1(X1))
      | ~ v4_orders_2(X0) ) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(X1,k3_orders_2(X0,X2,X3)),X2)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK2(X1,k3_orders_2(X0,X2,X3)),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,X2,X3)
      | ~ m1_subset_1(k3_orders_2(X0,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f46,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f26,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f44,f31])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f26,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (24593)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (24601)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (24602)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (24608)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (24609)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (24589)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (24611)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (24610)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (24601)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (24605)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (24603)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (24607)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (24592)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (24594)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (24591)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (24592)Refutation not found, incomplete strategy% (24592)------------------------------
% 0.21/0.50  % (24592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24592)Memory used [KB]: 10618
% 0.21/0.50  % (24592)Time elapsed: 0.092 s
% 0.21/0.50  % (24592)------------------------------
% 0.21/0.50  % (24592)------------------------------
% 0.21/0.51  % (24590)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (24595)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (24596)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (24606)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(resolution,[],[f79,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(global_subsumption,[],[f27,f28,f29,f30,f31,f46,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0)),
% 0.21/0.51    inference(resolution,[],[f71,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(resolution,[],[f68,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k3_orders_2(X0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1) | ~m1_subset_1(k3_orders_2(X0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | k1_xboole_0 = k3_orders_2(X0,k1_xboole_0,X1) | ~m1_subset_1(k3_orders_2(X0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(resolution,[],[f61,f39])).
% 0.21/0.51  % (24599)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(X0,k3_orders_2(X1,k1_xboole_0,X2)),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,k1_xboole_0,X2) | ~m1_subset_1(k3_orders_2(X1,k1_xboole_0,X2),k1_zfmisc_1(X0)) | ~v4_orders_2(X1)) )),
% 0.21/0.51    inference(resolution,[],[f56,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2(X1,k3_orders_2(X0,X2,X3)),u1_struct_0(X0)) | ~r1_tarski(X2,sK2(X1,k3_orders_2(X0,X2,X3))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,X2,X3) | ~m1_subset_1(k3_orders_2(X0,X2,X3),k1_zfmisc_1(X1)) | ~v4_orders_2(X0)) )),
% 0.21/0.51    inference(resolution,[],[f49,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X1,k3_orders_2(X0,X2,X3)),X2) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(sK2(X1,k3_orders_2(X0,X2,X3)),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,X2,X3) | ~m1_subset_1(k3_orders_2(X0,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(resolution,[],[f37,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f26,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f44,f31])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_orders_2(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.51    inference(resolution,[],[f34,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v5_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v4_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v3_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24601)------------------------------
% 0.21/0.51  % (24601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24601)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24601)Memory used [KB]: 10746
% 0.21/0.51  % (24601)Time elapsed: 0.090 s
% 0.21/0.51  % (24601)------------------------------
% 0.21/0.51  % (24601)------------------------------
% 0.21/0.51  % (24588)Success in time 0.152 s
%------------------------------------------------------------------------------
