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
% DateTime   : Thu Dec  3 13:09:46 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 273 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1190 expanded)
%              Number of equality atoms :   22 ( 165 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f86])).

fof(f86,plain,(
    ~ r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f68,f77,f83,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK1(X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & m1_subset_1(X3,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & m1_subset_1(X3,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => r2_hidden(X3,X2) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

fof(f83,plain,(
    ~ r1_tarski(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f64,f81,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,(
    r1_tarski(k2_orders_2(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,(
    u1_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f63])).

fof(f63,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f62,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

fof(f35,plain,(
    u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f34,f33,f32,f37,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f32,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f110,plain,(
    r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f109,f75])).

fof(f75,plain,(
    k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f34,f31,f30,f33,f32,f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f109,plain,(
    r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),a_2_1_orders_2(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f32,f31,f34,f33,f30,f37,f65,f87,f60])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | r2_hidden(X3,a_2_1_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | r2_hidden(sK3(X1,X2,X3),X2)
      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f87,plain,(
    m1_subset_1(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f68,f77,f83,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK1(X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (10813)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:49:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (10803)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.48  % (10811)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (10798)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (10792)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (10798)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(subsumption_resolution,[],[f110,f86])).
% 1.39/0.54  fof(f86,plain,(
% 1.39/0.54    ~r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f68,f77,f83,f42])).
% 1.39/0.54  fof(f42,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK1(X1,X2),X2) | r1_tarski(X1,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.54    inference(flattening,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X1) => r2_hidden(X3,X2)) => r1_tarski(X1,X2))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).
% 1.39/0.54  fof(f83,plain,(
% 1.39/0.54    ~r1_tarski(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f64,f81,f46])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    r1_tarski(k2_orders_2(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f77,f48])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.54  fof(f64,plain,(
% 1.39/0.54    u1_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0)),
% 1.39/0.54    inference(backward_demodulation,[],[f35,f63])).
% 1.39/0.54  fof(f63,plain,(
% 1.39/0.54    k1_xboole_0 = k1_struct_0(sK0)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f62,f38])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 1.39/0.54  fof(f62,plain,(
% 1.39/0.54    l1_struct_0(sK0)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f34,f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    l1_orders_2(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f15])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,negated_conjecture,(
% 1.39/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 1.39/0.54    inference(negated_conjecture,[],[f13])).
% 1.39/0.54  fof(f13,conjecture,(
% 1.39/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    u1_struct_0(sK0) != k2_orders_2(sK0,k1_struct_0(sK0))),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f30,f31,f34,f33,f32,f37,f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f23])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    v4_orders_2(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    v5_orders_2(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    v3_orders_2(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ~v2_struct_0(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f68,plain,(
% 1.39/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f57,f47])).
% 1.39/0.54  fof(f47,plain,(
% 1.39/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f57,plain,(
% 1.39/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f45])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f1])).
% 1.39/0.54  fof(f110,plain,(
% 1.39/0.54    r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),k2_orders_2(sK0,k1_xboole_0))),
% 1.39/0.54    inference(forward_demodulation,[],[f109,f75])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f34,f31,f30,f33,f32,f37,f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 1.39/0.54  fof(f109,plain,(
% 1.39/0.54    r2_hidden(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),a_2_1_orders_2(sK0,k1_xboole_0))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f32,f31,f34,f33,f30,f37,f65,f87,f60])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(sK3(X1,X2,X3),X2) | r2_hidden(X3,a_2_1_orders_2(X1,X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f51])).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | r2_hidden(sK3(X1,X2,X3),X2) | r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.39/0.54    inference(flattening,[],[f26])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f12])).
% 1.39/0.54  fof(f12,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.39/0.54  fof(f87,plain,(
% 1.39/0.54    m1_subset_1(sK1(u1_struct_0(sK0),k2_orders_2(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f68,f77,f83,f41])).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK1(X1,X2),X1) | r1_tarski(X1,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f36,f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  % (10813)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (10798)------------------------------
% 1.39/0.55  % (10798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (10798)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (10798)Memory used [KB]: 1663
% 1.39/0.55  % (10798)Time elapsed: 0.100 s
% 1.39/0.55  % (10798)------------------------------
% 1.39/0.55  % (10798)------------------------------
% 1.39/0.55  % (10790)Success in time 0.182 s
%------------------------------------------------------------------------------
