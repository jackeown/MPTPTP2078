%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 (5882 expanded)
%              Number of leaves         :    5 (1005 expanded)
%              Depth                    :   34
%              Number of atoms          :  487 (37722 expanded)
%              Number of equality atoms :   58 ( 859 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(resolution,[],[f219,f267])).

fof(f267,plain,(
    ! [X2] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ),
    inference(subsumption_resolution,[],[f266,f265])).

fof(f265,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f262,f252])).

fof(f252,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f251,f109])).

fof(f109,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f108,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f108,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f107,f24])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f107,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f106,f23])).

fof(f23,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f106,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f105,f22])).

fof(f22,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f105,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f104,f21])).

fof(f21,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f104,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f17,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f17,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f251,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f250,f219])).

fof(f250,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f249,f24])).

fof(f249,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f248,f23])).

fof(f248,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f247,f22])).

fof(f247,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f246,f21])).

fof(f246,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f236,f20])).

fof(f236,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f217,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

% (2878)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f217,plain,(
    m1_orders_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f17,f216])).

fof(f216,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f215,f109])).

fof(f215,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f211,f19])).

fof(f211,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f210,f99])).

fof(f99,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(X2,sK2,sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f18,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f18,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f210,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f208,f184])).

fof(f184,plain,(
    m1_subset_1(sK4(u1_struct_0(sK0),sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f182,f19])).

fof(f182,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(u1_struct_0(sK0),sK2,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f97,f109])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,sK2,sK1),X0) ) ),
    inference(resolution,[],[f18,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f208,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK1)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK2,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f205,f194])).

fof(f194,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f192,f19])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK2) ),
    inference(resolution,[],[f98,f109])).

% (2862)Refutation not found, incomplete strategy% (2862)------------------------------
% (2862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f98,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | r2_hidden(sK4(X1,sK2,sK1),sK2) ) ),
    inference(resolution,[],[f18,f35])).

% (2862)Termination reason: Refutation not found, incomplete strategy

% (2862)Memory used [KB]: 10618
fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

% (2862)Time elapsed: 0.072 s
% (2862)------------------------------
% (2862)------------------------------
fof(f205,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f204,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f115,f109])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f114,f19])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f113,f24])).

fof(f113,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f112,f23])).

fof(f112,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f111,f22])).

fof(f111,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f110,f21])).

fof(f110,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f101,f20])).

fof(f101,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f17,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f204,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f202,f19])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f96,f130])).

fof(f130,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f129,f109])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f128,f19])).

fof(f128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f127,f24])).

fof(f127,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f126,f23])).

fof(f126,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f125,f22])).

fof(f125,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f124,f21])).

fof(f124,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f103,f20])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f17,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f95,f23])).

fof(f95,plain,(
    ! [X4,X5,X3] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f94,f22])).

fof(f94,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,(
    ! [X4,X5,X3] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(subsumption_resolution,[],[f84,f20])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,k3_orders_2(sK0,X5,X4)) ) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f262,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r2_hidden(sK4(X1,sK2,k1_xboole_0),sK2) ) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r2_hidden(sK4(X1,sK2,k1_xboole_0),sK2)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(backward_demodulation,[],[f226,f252])).

fof(f226,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1,sK2,k1_xboole_0),sK2)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f221,f216])).

fof(f221,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | r2_hidden(sK4(X1,sK2,sK1),sK2) ) ),
    inference(backward_demodulation,[],[f98,f216])).

fof(f266,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ) ),
    inference(forward_demodulation,[],[f261,f252])).

fof(f261,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | ~ r2_hidden(sK4(X2,sK2,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | ~ r2_hidden(sK4(X2,sK2,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ) ),
    inference(backward_demodulation,[],[f227,f252])).

fof(f227,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(X2,sK2,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) ) ),
    inference(forward_demodulation,[],[f222,f216])).

fof(f222,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | ~ r2_hidden(sK4(X2,sK2,sK1),sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) ) ),
    inference(backward_demodulation,[],[f99,f216])).

fof(f219,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f19,f216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (2863)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.45  % (2879)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (2866)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (2861)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (2861)Refutation not found, incomplete strategy% (2861)------------------------------
% 0.20/0.47  % (2861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (2861)Memory used [KB]: 6140
% 0.20/0.47  % (2861)Time elapsed: 0.052 s
% 0.20/0.47  % (2861)------------------------------
% 0.20/0.47  % (2861)------------------------------
% 0.20/0.47  % (2877)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (2869)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (2870)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (2876)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (2865)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (2881)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (2868)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (2874)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (2862)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (2864)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (2874)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(resolution,[],[f219,f267])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f266,f265])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(sK4(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f262,f252])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f251,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f108,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f107,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    l1_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f106,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v5_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    v4_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f104,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v3_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f100,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f17,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    m1_orders_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f251,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f250,f219])).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f249,f24])).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    ~l1_orders_2(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f248,f23])).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f247,f22])).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f246,f21])).
% 0.20/0.48  fof(f246,plain,(
% 0.20/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(subsumption_resolution,[],[f236,f20])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2),
% 0.20/0.48    inference(resolution,[],[f217,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % (2878)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    m1_orders_2(sK2,sK0,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f17,f216])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f215,f109])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f211,f19])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f210,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(sK4(X2,sK2,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(resolution,[],[f18,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1,X2),X2) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK1) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f208,f184])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    m1_subset_1(sK4(u1_struct_0(sK0),sK2,sK1),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f19])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(u1_struct_0(sK0),sK2,sK1),u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f97,f109])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,sK2,sK1),X0)) )),
% 0.20/0.48    inference(resolution,[],[f18,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK1) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK2,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(resolution,[],[f205,f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f192,f19])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK2,sK1),sK2)),
% 0.20/0.48    inference(resolution,[],[f98,f109])).
% 0.20/0.48  % (2862)Refutation not found, incomplete strategy% (2862)------------------------------
% 0.20/0.48  % (2862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | r2_hidden(sK4(X1,sK2,sK1),sK2)) )),
% 0.20/0.48    inference(resolution,[],[f18,f35])).
% 0.20/0.48  % (2862)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (2862)Memory used [KB]: 10618
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % (2862)Time elapsed: 0.072 s
% 0.20/0.48  % (2862)------------------------------
% 0.20/0.48  % (2862)------------------------------
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK1) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f204,f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f115,f109])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f114,f19])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f113,f24])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f23])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f111,f22])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f110,f21])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f20])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f17,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK1) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f202,f19])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK1) )),
% 0.20/0.48    inference(superposition,[],[f96,f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f129,f109])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f128,f19])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f127,f24])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f126,f23])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f125,f22])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f124,f21])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f103,f20])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.48    inference(resolution,[],[f17,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_orders_2(sK0,X5,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f23])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~v5_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f94,f22])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f93,f21])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f20])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X5) | ~r2_hidden(X3,k3_orders_2(sK0,X5,X4))) )),
% 0.20/0.48    inference(resolution,[],[f24,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r2_hidden(sK4(X1,sK2,k1_xboole_0),sK2)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f259])).
% 0.20/0.48  fof(f259,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r2_hidden(sK4(X1,sK2,k1_xboole_0),sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f226,f252])).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(sK4(X1,sK2,k1_xboole_0),sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f221,f216])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(X1)) | r2_hidden(sK4(X1,sK2,sK1),sK2)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f98,f216])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(sK4(X2,k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f261,f252])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | ~r2_hidden(sK4(X2,sK2,k1_xboole_0),k1_xboole_0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f260])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | ~r2_hidden(sK4(X2,sK2,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f227,f252])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(sK4(X2,sK2,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f222,f216])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | ~r2_hidden(sK4(X2,sK2,sK1),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(X2))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f99,f216])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(backward_demodulation,[],[f19,f216])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (2874)------------------------------
% 0.20/0.48  % (2874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2874)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (2874)Memory used [KB]: 1663
% 0.20/0.48  % (2874)Time elapsed: 0.078 s
% 0.20/0.48  % (2874)------------------------------
% 0.20/0.48  % (2874)------------------------------
% 0.20/0.48  % (2860)Success in time 0.131 s
%------------------------------------------------------------------------------
