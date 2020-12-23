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
% DateTime   : Thu Dec  3 13:09:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 409 expanded)
%              Number of leaves         :   12 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  380 (1699 expanded)
%              Number of equality atoms :   48 ( 278 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f793,plain,(
    $false ),
    inference(subsumption_resolution,[],[f791,f129])).

fof(f129,plain,(
    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f34,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(f127,plain,
    ( r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f123,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f112,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f112,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,k1_orders_2(sK0,X3))
      | r2_hidden(X4,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f109,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f109,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f108,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f33])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f32])).

fof(f32,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f105,f31])).

fof(f31,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f30])).

fof(f30,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f47,f62])).

fof(f62,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f37,f61])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

% (4134)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f791,plain,(
    ~ r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(resolution,[],[f788,f122])).

fof(f122,plain,(
    ~ r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) ),
    inference(resolution,[],[f119,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X0) ) ),
    inference(forward_demodulation,[],[f68,f62])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X0) ) ),
    inference(resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 != X2
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f119,plain,(
    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f111,f60])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_orders_2(sK0,X1))
      | m1_subset_1(X2,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f109,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f788,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f787,f154])).

fof(f154,plain,(
    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f152,f34])).

fof(f152,plain,
    ( sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f151,f45])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK2(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f147,f99])).

fof(f99,plain,(
    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f98,f60])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(forward_demodulation,[],[f97,f62])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f96,f33])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f95,f29])).

fof(f95,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f94,f31])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f147,plain,(
    ! [X0] :
      ( sK2(X0,sK0,k2_struct_0(sK0)) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f146,f60])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f145,f62])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f144,f33])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f143,f29])).

fof(f143,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f142,f31])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f141,f30])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f787,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f782,f34])).

fof(f782,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))
      | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f781,f45])).

fof(f781,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f775,f99])).

fof(f775,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f774,f60])).

fof(f774,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f773,f62])).

fof(f773,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f772,f54])).

fof(f772,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f771,f33])).

fof(f771,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f770,f29])).

fof(f770,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f769,f31])).

fof(f769,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f768,f30])).

fof(f768,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK2(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,X4,sK2(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (4127)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (4127)Refutation not found, incomplete strategy% (4127)------------------------------
% 0.22/0.50  % (4127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4135)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (4127)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (4127)Memory used [KB]: 10618
% 0.22/0.50  % (4127)Time elapsed: 0.062 s
% 0.22/0.50  % (4127)------------------------------
% 0.22/0.50  % (4127)------------------------------
% 0.22/0.55  % (4132)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (4120)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (4124)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (4119)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (4129)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (4137)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.56  % (4128)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  % (4140)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (4135)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f793,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f791,f129])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f127,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.22/0.56    inference(negated_conjecture,[],[f12])).
% 0.22/0.56  fof(f12,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f123,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f112,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f36,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,k1_orders_2(sK0,X3)) | r2_hidden(X4,k2_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f109,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f108,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ~v2_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f107,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    l1_orders_2(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f106,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    v5_orders_2(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f105,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    v4_orders_2(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f104,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    v3_orders_2(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.56    inference(superposition,[],[f47,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f37,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    l1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f38,f33])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  % (4134)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 0.22/0.56  fof(f791,plain,(
% 0.22/0.56    ~r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f788,f122])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ~r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))),
% 0.22/0.56    inference(resolution,[],[f119,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f68,f62])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f59,f33])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.22/0.56    inference(equality_resolution,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f117,f34])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f113,f45])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(X0,k2_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f111,f60])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,k1_orders_2(sK0,X1)) | m1_subset_1(X2,k2_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f109,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.56  fof(f788,plain,(
% 0.22/0.56    ( ! [X0] : (r2_orders_2(sK0,X0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f787,f154])).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f152,f34])).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f151,f45])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | sK2(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 0.22/0.56    inference(forward_demodulation,[],[f147,f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f98,f60])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f97,f62])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f96,f33])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f95,f29])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f94,f31])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X0] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f93,f30])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f42,f32])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    ( ! [X0] : (sK2(X0,sK0,k2_struct_0(sK0)) = X0 | ~r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.22/0.56    inference(resolution,[],[f146,f60])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f145,f62])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f144,f33])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f143,f29])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f142,f31])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f141,f30])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(resolution,[],[f53,f32])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.22/0.56  fof(f787,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f782,f34])).
% 0.22/0.56  fof(f782,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f781,f45])).
% 0.22/0.56  fof(f781,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0)))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f775,f99])).
% 0.22/0.56  fof(f775,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(X1,sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,a_2_0_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.22/0.56    inference(resolution,[],[f774,f60])).
% 0.22/0.56  fof(f774,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f773,f62])).
% 0.22/0.56  fof(f773,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f772,f54])).
% 0.22/0.56  fof(f772,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f771,f33])).
% 0.22/0.56  fof(f771,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f770,f29])).
% 0.22/0.56  fof(f770,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f769,f31])).
% 0.22/0.56  fof(f769,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f768,f30])).
% 0.22/0.56  fof(f768,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK2(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.56    inference(resolution,[],[f51,f32])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~v5_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,X4,sK2(X0,X1,X2)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (4135)------------------------------
% 0.22/0.56  % (4135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4135)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (4135)Memory used [KB]: 3070
% 0.22/0.56  % (4135)Time elapsed: 0.132 s
% 0.22/0.56  % (4135)------------------------------
% 0.22/0.56  % (4135)------------------------------
% 0.22/0.57  % (4115)Success in time 0.203 s
%------------------------------------------------------------------------------
