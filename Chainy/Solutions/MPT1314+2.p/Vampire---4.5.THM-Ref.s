%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1314+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:17 EST 2020

% Result     : Theorem 46.23s
% Output     : Refutation 46.70s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 365 expanded)
%              Number of leaves         :   10 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  231 (1677 expanded)
%              Number of equality atoms :   36 ( 221 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28048,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28047,f26958])).

fof(f26958,plain,(
    ~ sP30(sK1,sK2,sK0) ),
    inference(subsumption_resolution,[],[f26950,f3087])).

fof(f3087,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2389])).

fof(f2389,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2388])).

fof(f2388,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2368])).

fof(f2368,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2367])).

fof(f2367,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f26950,plain,
    ( ~ sP30(sK1,sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f5797,f3090])).

fof(f3090,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2389])).

fof(f5797,plain,(
    ! [X78] :
      ( ~ l1_pre_topc(X78)
      | ~ sP30(sK1,sK2,X78)
      | ~ m1_pre_topc(sK2,X78) ) ),
    inference(subsumption_resolution,[],[f5796,f4655])).

fof(f4655,plain,(
    ~ r2_hidden(sK1,u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f4654,f4172])).

fof(f4172,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f3084,f3085])).

fof(f3085,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f2389])).

fof(f3084,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2389])).

fof(f4654,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f4639,f4497])).

fof(f4497,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f4477,f3090])).

fof(f4477,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f3087,f3218])).

fof(f3218,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f2482])).

fof(f2482,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4639,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK2)) ),
    inference(resolution,[],[f4171,f3182])).

fof(f3182,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f2454])).

fof(f2454,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1774])).

fof(f1774,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f4171,plain,(
    ~ v3_pre_topc(sK1,sK2) ),
    inference(forward_demodulation,[],[f3086,f3085])).

fof(f3086,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f2389])).

fof(f5796,plain,(
    ! [X78] :
      ( ~ l1_pre_topc(X78)
      | ~ sP30(sK1,sK2,X78)
      | r2_hidden(sK1,u1_pre_topc(sK2))
      | ~ m1_pre_topc(sK2,X78) ) ),
    inference(subsumption_resolution,[],[f5445,f4497])).

fof(f5445,plain,(
    ! [X78] :
      ( ~ l1_pre_topc(X78)
      | ~ l1_pre_topc(sK2)
      | ~ sP30(sK1,sK2,X78)
      | r2_hidden(sK1,u1_pre_topc(sK2))
      | ~ m1_pre_topc(sK2,X78) ) ),
    inference(resolution,[],[f4172,f3224])).

fof(f3224,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP30(X2,X1,X0)
      | r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f2485])).

fof(f2485,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1776])).

fof(f1776,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f28047,plain,(
    sP30(sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f28046,f27154])).

fof(f27154,plain,(
    sK1 = k3_xboole_0(sK1,k2_struct_0(sK2)) ),
    inference(resolution,[],[f8292,f3310])).

fof(f3310,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2551])).

fof(f2551,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f8292,plain,(
    r1_tarski(sK1,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f8291,f5927])).

fof(f5927,plain,(
    sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f5926,f5795])).

fof(f5795,plain,(
    m1_pre_topc(k1_pre_topc(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f5440,f4497])).

fof(f5440,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(k1_pre_topc(sK2,sK1),sK2) ),
    inference(resolution,[],[f4172,f3196])).

fof(f3196,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2463])).

fof(f2463,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2462])).

fof(f2462,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1778])).

fof(f1778,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f5926,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK1),sK2)
    | sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f5925,f5794])).

fof(f5794,plain,(
    v1_pre_topc(k1_pre_topc(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f5439,f4497])).

fof(f5439,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_pre_topc(k1_pre_topc(sK2,sK1)) ),
    inference(resolution,[],[f4172,f3195])).

fof(f3195,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2463])).

fof(f5925,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK2,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK1),sK2)
    | sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f5594,f4497])).

fof(f5594,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_pre_topc(k1_pre_topc(sK2,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK2,sK1),sK2)
    | sK1 = k2_struct_0(k1_pre_topc(sK2,sK1)) ),
    inference(resolution,[],[f4172,f4109])).

fof(f4109,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f3210])).

fof(f3210,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2476])).

fof(f2476,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2475])).

fof(f2475,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1768])).

fof(f1768,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f8291,plain,(
    r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK1)),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8290,f8280])).

fof(f8280,plain,(
    l1_pre_topc(k1_pre_topc(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f8248,f4497])).

fof(f8248,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(k1_pre_topc(sK2,sK1)) ),
    inference(resolution,[],[f5795,f3218])).

fof(f8290,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK2,sK1))
    | r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK1)),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8252,f4497])).

fof(f8252,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK1))
    | r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK1)),k2_struct_0(sK2)) ),
    inference(resolution,[],[f5795,f3229])).

fof(f3229,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f2485])).

fof(f28046,plain,(
    sP30(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2,sK0) ),
    inference(forward_demodulation,[],[f28015,f3535])).

fof(f3535,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28015,plain,(
    sP30(k3_xboole_0(k2_struct_0(sK2),sK1),sK2,sK0) ),
    inference(superposition,[],[f5235,f5992])).

fof(f5992,plain,(
    ! [X251] : k3_xboole_0(X251,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X251) ),
    inference(backward_demodulation,[],[f5687,f5688])).

fof(f5688,plain,(
    ! [X252] : k3_xboole_0(X252,sK1) = k9_subset_1(u1_struct_0(sK2),X252,sK1) ),
    inference(resolution,[],[f4172,f3670])).

fof(f3670,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2829])).

fof(f2829,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f5687,plain,(
    ! [X251] : k9_subset_1(u1_struct_0(sK2),X251,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X251) ),
    inference(resolution,[],[f4172,f3669])).

fof(f3669,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2828])).

fof(f2828,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f454])).

fof(f454,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f5235,plain,(
    ! [X169] : sP30(k9_subset_1(u1_struct_0(X169),sK1,k2_struct_0(X169)),X169,sK0) ),
    inference(subsumption_resolution,[],[f4899,f4609])).

fof(f4609,plain,(
    r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f4608,f3089])).

fof(f3089,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2389])).

fof(f4608,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f4541,f3090])).

fof(f4541,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f3088,f3183])).

fof(f3183,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f2454])).

fof(f3088,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2389])).

fof(f4899,plain,(
    ! [X169] :
      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
      | sP30(k9_subset_1(u1_struct_0(X169),sK1,k2_struct_0(X169)),X169,sK0) ) ),
    inference(resolution,[],[f3089,f4113])).

fof(f4113,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | sP30(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X0) ) ),
    inference(equality_resolution,[],[f3220])).

fof(f3220,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | sP30(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f2485])).
%------------------------------------------------------------------------------
