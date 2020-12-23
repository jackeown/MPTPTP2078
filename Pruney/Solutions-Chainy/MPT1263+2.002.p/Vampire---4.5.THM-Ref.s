%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:16 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  203 (8220 expanded)
%              Number of leaves         :   19 (1660 expanded)
%              Depth                    :   48
%              Number of atoms          :  787 (44142 expanded)
%              Number of equality atoms :  158 (7404 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f651,plain,(
    $false ),
    inference(subsumption_resolution,[],[f650,f358])).

fof(f358,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f355,f43])).

fof(f43,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

fof(f355,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f354,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f354,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f353,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f353,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f349,f103])).

fof(f103,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f349,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(superposition,[],[f58,f342])).

fof(f342,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f341,f232])).

fof(f232,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f227,f46])).

fof(f227,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f163,f220])).

fof(f220,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f218,f103])).

fof(f218,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f217,f48])).

fof(f217,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f216,f46])).

fof(f216,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f211,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f211,plain,
    ( v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f210,f46])).

fof(f210,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f207,f168])).

fof(f168,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f167,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f165,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f78,f48])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0))
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(X1,sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f207,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f203,f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f163,f45])).

fof(f45,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,X2)
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f203,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f202,f101])).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f200,f148])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f163,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f162,f101])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f160,f148])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f341,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f340,f46])).

fof(f340,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f331,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f331,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f328])).

fof(f328,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f323,f231])).

fof(f231,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f228,f46])).

fof(f228,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f168,f220])).

fof(f323,plain,(
    ! [X6,X5] :
      ( ~ r1_xboole_0(X6,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f318,f302])).

fof(f302,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),X2)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f300,f50])).

fof(f300,plain,(
    ! [X2] :
      ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),X2) ) ),
    inference(resolution,[],[f297,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f297,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f296,f46])).

fof(f296,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f292,f220])).

fof(f292,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f291,f101])).

fof(f291,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f289,f148])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f75,f48])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f318,plain,(
    ! [X6,X5] :
      ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | ~ r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),X5)
      | ~ r1_xboole_0(X6,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f302,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f194,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f650,plain,(
    ~ v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f646,f356])).

fof(f356,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f355,f41])).

fof(f41,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f646,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f611,f357])).

fof(f357,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f355,f44])).

fof(f44,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f611,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f598,f351])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f350,f84])).

fof(f350,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f343,f46])).

fof(f343,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(sK1,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f195,f342])).

fof(f598,plain,(
    ! [X2] : r2_hidden(sK4(sK0,k1_xboole_0,sK2),X2) ),
    inference(subsumption_resolution,[],[f595,f50])).

fof(f595,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
      | r2_hidden(sK4(sK0,k1_xboole_0,sK2),X2) ) ),
    inference(resolution,[],[f591,f84])).

fof(f591,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f590,f357])).

fof(f590,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f589,f356])).

fof(f589,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f570,f358])).

fof(f570,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f564,f351])).

fof(f564,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)
    | r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f556,f359])).

fof(f359,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f355,f42])).

fof(f42,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f556,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)
    | r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(resolution,[],[f552,f356])).

fof(f552,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f551])).

fof(f551,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f550,f139])).

fof(f139,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f134,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f132,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f132,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f131,f50])).

fof(f131,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f130,f106])).

fof(f106,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f105,f103])).

fof(f105,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f130,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(superposition,[],[f129,f124])).

fof(f124,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f123,f100])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f90,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f90,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f52,f88])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f82,f81])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f123,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f120,f89])).

fof(f120,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f92,f50])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f83,f88])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f129,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f60,f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f550,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | k2_pre_topc(sK0,k1_xboole_0) = X0 ) ),
    inference(subsumption_resolution,[],[f548,f50])).

fof(f548,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f545,f148])).

fof(f545,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f544])).

fof(f544,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f543,f139])).

fof(f543,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | k2_pre_topc(sK0,k1_xboole_0) = X0 ) ),
    inference(subsumption_resolution,[],[f541,f50])).

fof(f541,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f540])).

fof(f540,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f510,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),sK6(sK0,k1_xboole_0,sK4(sK0,X0,X1)))
      | r2_hidden(sK4(sK0,X0,X1),k1_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f183,f148])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f182,f48])).

fof(f182,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f181,f50])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f96,f139])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | r2_hidden(X3,sK6(X0,X1,X3))
      | r2_hidden(X3,k2_pre_topc(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | r2_hidden(X3,sK6(X0,X1,X3))
      | r2_hidden(X3,X2)
      | k2_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f510,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X9
      | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9)
      | ~ r2_hidden(X10,u1_struct_0(sK0))
      | r2_hidden(X10,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f509,f139])).

fof(f509,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10))
      | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9)
      | k2_pre_topc(sK0,k1_xboole_0) = X9
      | ~ r2_hidden(X10,u1_struct_0(sK0))
      | r2_hidden(X10,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f508,f191])).

fof(f191,plain,(
    ! [X0] :
      ( v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f190,f48])).

fof(f190,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f189,f50])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f97,f139])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | v3_pre_topc(sK6(X0,X1,X3),X0)
      | r2_hidden(X3,k2_pre_topc(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | v3_pre_topc(sK6(X0,X1,X3),X0)
      | r2_hidden(X3,X2)
      | k2_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f508,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK6(sK0,k1_xboole_0,X10),sK0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10))
      | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9)
      | k2_pre_topc(sK0,k1_xboole_0) = X9
      | ~ r2_hidden(X10,u1_struct_0(sK0))
      | r2_hidden(X10,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f507,f238])).

fof(f238,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f237,f48])).

fof(f237,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f236,f50])).

fof(f236,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f98,f139])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X3,k2_pre_topc(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X3,X2)
      | k2_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f507,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK6(sK0,k1_xboole_0,X10),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK6(sK0,k1_xboole_0,X10),sK0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10))
      | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9)
      | k2_pre_topc(sK0,k1_xboole_0) = X9
      | ~ r2_hidden(X10,u1_struct_0(sK0))
      | r2_hidden(X10,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f500,f50])).

fof(f500,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK6(sK0,k1_xboole_0,X10),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK6(sK0,k1_xboole_0,X10),sK0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9)
      | k2_pre_topc(sK0,k1_xboole_0) = X9
      | ~ r2_hidden(X10,u1_struct_0(sK0))
      | r2_hidden(X10,k1_xboole_0) ) ),
    inference(resolution,[],[f432,f178])).

fof(f178,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f177,f48])).

fof(f177,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f176,f50])).

fof(f176,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f95,f139])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | r1_xboole_0(X1,sK6(X0,X1,X3))
      | r2_hidden(X3,k2_pre_topc(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | r1_xboole_0(X1,sK6(X0,X1,X3))
      | r2_hidden(X3,X2)
      | k2_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f432,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),X1)
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f77,f48])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X4,X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X4)
      | ~ r1_xboole_0(X1,X4)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:24:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (20209)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (20201)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (20193)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (20195)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (20187)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (20196)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (20200)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20191)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (20186)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20213)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (20188)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (20208)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (20188)Refutation not found, incomplete strategy% (20188)------------------------------
% 0.22/0.54  % (20188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20189)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (20192)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20206)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (20212)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (20190)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.55  % (20208)Refutation not found, incomplete strategy% (20208)------------------------------
% 1.36/0.55  % (20208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (20208)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (20208)Memory used [KB]: 10874
% 1.36/0.55  % (20208)Time elapsed: 0.131 s
% 1.36/0.55  % (20208)------------------------------
% 1.36/0.55  % (20208)------------------------------
% 1.36/0.55  % (20197)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (20204)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (20198)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (20215)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (20194)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.56  % (20194)Refutation not found, incomplete strategy% (20194)------------------------------
% 1.36/0.56  % (20194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (20194)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (20194)Memory used [KB]: 10746
% 1.36/0.56  % (20194)Time elapsed: 0.140 s
% 1.36/0.56  % (20194)------------------------------
% 1.36/0.56  % (20194)------------------------------
% 1.36/0.56  % (20188)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (20188)Memory used [KB]: 10746
% 1.36/0.56  % (20188)Time elapsed: 0.126 s
% 1.36/0.56  % (20188)------------------------------
% 1.36/0.56  % (20188)------------------------------
% 1.36/0.56  % (20210)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.56  % (20211)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.56  % (20202)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.56  % (20203)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.56  % (20205)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.56  % (20212)Refutation not found, incomplete strategy% (20212)------------------------------
% 1.36/0.56  % (20212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (20214)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.57  % (20203)Refutation not found, incomplete strategy% (20203)------------------------------
% 1.57/0.57  % (20203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (20196)Refutation not found, incomplete strategy% (20196)------------------------------
% 1.57/0.57  % (20196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (20203)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (20203)Memory used [KB]: 10746
% 1.57/0.57  % (20203)Time elapsed: 0.161 s
% 1.57/0.57  % (20203)------------------------------
% 1.57/0.57  % (20203)------------------------------
% 1.57/0.57  % (20199)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.58  % (20207)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.58  % (20196)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (20196)Memory used [KB]: 11001
% 1.57/0.58  % (20196)Time elapsed: 0.159 s
% 1.57/0.58  % (20196)------------------------------
% 1.57/0.58  % (20196)------------------------------
% 1.57/0.58  % (20212)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (20212)Memory used [KB]: 10874
% 1.57/0.58  % (20212)Time elapsed: 0.152 s
% 1.57/0.58  % (20212)------------------------------
% 1.57/0.58  % (20212)------------------------------
% 1.57/0.60  % (20192)Refutation found. Thanks to Tanya!
% 1.57/0.60  % SZS status Theorem for theBenchmark
% 1.57/0.60  % SZS output start Proof for theBenchmark
% 1.57/0.60  fof(f651,plain,(
% 1.57/0.60    $false),
% 1.57/0.60    inference(subsumption_resolution,[],[f650,f358])).
% 1.57/0.60  fof(f358,plain,(
% 1.57/0.60    v3_pre_topc(sK2,sK0)),
% 1.57/0.60    inference(resolution,[],[f355,f43])).
% 1.57/0.60  fof(f43,plain,(
% 1.57/0.60    ~v1_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f24,plain,(
% 1.57/0.60    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.57/0.60    inference(flattening,[],[f23])).
% 1.57/0.60  fof(f23,plain,(
% 1.57/0.60    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f22])).
% 1.57/0.60  fof(f22,negated_conjecture,(
% 1.57/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 1.57/0.60    inference(negated_conjecture,[],[f21])).
% 1.57/0.60  fof(f21,conjecture,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).
% 1.57/0.60  fof(f355,plain,(
% 1.57/0.60    v1_tops_1(sK1,sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f354,f48])).
% 1.57/0.60  fof(f48,plain,(
% 1.57/0.60    l1_pre_topc(sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f354,plain,(
% 1.57/0.60    ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f353,f46])).
% 1.57/0.60  fof(f46,plain,(
% 1.57/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f353,plain,(
% 1.57/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f349,f103])).
% 1.57/0.60  fof(f103,plain,(
% 1.57/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.57/0.60    inference(resolution,[],[f102,f48])).
% 1.57/0.60  fof(f102,plain,(
% 1.57/0.60    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.57/0.60    inference(resolution,[],[f54,f55])).
% 1.57/0.60  fof(f55,plain,(
% 1.57/0.60    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f26])).
% 1.57/0.60  fof(f26,plain,(
% 1.57/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f15])).
% 1.57/0.60  fof(f15,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.57/0.60  fof(f54,plain,(
% 1.57/0.60    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f25])).
% 1.57/0.60  fof(f25,plain,(
% 1.57/0.60    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f14])).
% 1.57/0.60  fof(f14,axiom,(
% 1.57/0.60    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.57/0.60  fof(f349,plain,(
% 1.57/0.60    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 1.57/0.60    inference(superposition,[],[f58,f342])).
% 1.57/0.60  fof(f342,plain,(
% 1.57/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f341,f232])).
% 1.57/0.60  fof(f232,plain,(
% 1.57/0.60    v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f227,f46])).
% 1.57/0.60  fof(f227,plain,(
% 1.57/0.60    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f226])).
% 1.57/0.60  fof(f226,plain,(
% 1.57/0.60    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(superposition,[],[f163,f220])).
% 1.57/0.60  fof(f220,plain,(
% 1.57/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f219])).
% 1.57/0.60  fof(f219,plain,(
% 1.57/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(forward_demodulation,[],[f218,f103])).
% 1.57/0.60  fof(f218,plain,(
% 1.57/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f217,f48])).
% 1.57/0.60  fof(f217,plain,(
% 1.57/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f216,f46])).
% 1.57/0.60  fof(f216,plain,(
% 1.57/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.57/0.60    inference(resolution,[],[f211,f59])).
% 1.57/0.60  fof(f59,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f29])).
% 1.57/0.60  fof(f29,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f18])).
% 1.57/0.60  fof(f18,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.57/0.60  fof(f211,plain,(
% 1.57/0.60    v1_tops_1(sK1,sK0) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f210,f46])).
% 1.57/0.60  fof(f210,plain,(
% 1.57/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f208])).
% 1.57/0.60  fof(f208,plain,(
% 1.57/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(resolution,[],[f207,f168])).
% 1.57/0.60  fof(f168,plain,(
% 1.57/0.60    ( ! [X0] : (r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f167,f101])).
% 1.57/0.60  fof(f101,plain,(
% 1.57/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.57/0.60    inference(forward_demodulation,[],[f53,f49])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f6])).
% 1.57/0.60  fof(f6,axiom,(
% 1.57/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.57/0.60  fof(f53,plain,(
% 1.57/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.57/0.60  fof(f167,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f166])).
% 1.57/0.60  fof(f166,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(resolution,[],[f165,f148])).
% 1.57/0.60  fof(f148,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f78,f48])).
% 1.57/0.60  fof(f78,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) | k2_pre_topc(X0,X1) = X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(flattening,[],[f33])).
% 1.57/0.60  fof(f33,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f13])).
% 1.57/0.60  fof(f13,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).
% 1.57/0.60  fof(f165,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f76,f48])).
% 1.57/0.60  fof(f76,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(X1,sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f207,plain,(
% 1.57/0.60    ( ! [X0] : (~r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f204])).
% 1.57/0.60  fof(f204,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 1.57/0.60    inference(resolution,[],[f203,f164])).
% 1.57/0.60  fof(f164,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 1.57/0.60    inference(resolution,[],[f163,f45])).
% 1.57/0.60  fof(f45,plain,(
% 1.57/0.60    ( ! [X2] : (~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,X2) | v1_tops_1(sK1,sK0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f203,plain,(
% 1.57/0.60    ( ! [X0] : (m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f202,f101])).
% 1.57/0.60  fof(f202,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f201])).
% 1.57/0.60  fof(f201,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(resolution,[],[f200,f148])).
% 1.57/0.60  fof(f200,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f73,f48])).
% 1.57/0.60  fof(f73,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f163,plain,(
% 1.57/0.60    ( ! [X0] : (v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f162,f101])).
% 1.57/0.60  fof(f162,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f161])).
% 1.57/0.60  fof(f161,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(resolution,[],[f160,f148])).
% 1.57/0.60  fof(f160,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f74,f48])).
% 1.57/0.60  fof(f74,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f341,plain,(
% 1.57/0.60    ~v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f340,f46])).
% 1.57/0.60  fof(f340,plain,(
% 1.57/0.60    ~v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.60    inference(subsumption_resolution,[],[f331,f50])).
% 1.57/0.60  fof(f50,plain,(
% 1.57/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f10])).
% 1.57/0.60  fof(f10,axiom,(
% 1.57/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.57/0.60  fof(f331,plain,(
% 1.57/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f328])).
% 1.57/0.60  fof(f328,plain,(
% 1.57/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(resolution,[],[f323,f231])).
% 1.57/0.60  fof(f231,plain,(
% 1.57/0.60    r1_xboole_0(sK1,k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f228,f46])).
% 1.57/0.60  fof(f228,plain,(
% 1.57/0.60    r1_xboole_0(sK1,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f224])).
% 1.57/0.60  fof(f224,plain,(
% 1.57/0.60    r1_xboole_0(sK1,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(superposition,[],[f168,f220])).
% 1.57/0.60  fof(f323,plain,(
% 1.57/0.60    ( ! [X6,X5] : (~r1_xboole_0(X6,X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X5,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f318,f302])).
% 1.57/0.60  fof(f302,plain,(
% 1.57/0.60    ( ! [X2] : (r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),X2) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f300,f50])).
% 1.57/0.60  fof(f300,plain,(
% 1.57/0.60    ( ! [X2] : (u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),X2)) )),
% 1.57/0.60    inference(resolution,[],[f297,f84])).
% 1.57/0.60  fof(f84,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f38])).
% 1.57/0.60  fof(f38,plain,(
% 1.57/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f9])).
% 1.57/0.60  fof(f9,axiom,(
% 1.57/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.57/0.60  fof(f297,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(subsumption_resolution,[],[f296,f46])).
% 1.57/0.60  fof(f296,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f295])).
% 1.57/0.60  fof(f295,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.57/0.60    inference(superposition,[],[f292,f220])).
% 1.57/0.60  fof(f292,plain,(
% 1.57/0.60    ( ! [X0] : (r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f291,f101])).
% 1.57/0.60  fof(f291,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f290])).
% 1.57/0.60  fof(f290,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.57/0.60    inference(resolution,[],[f289,f148])).
% 1.57/0.60  fof(f289,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f75,f48])).
% 1.57/0.60  fof(f75,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f318,plain,(
% 1.57/0.60    ( ! [X6,X5] : (u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X5,sK0) | ~r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),X5) | ~r1_xboole_0(X6,X5) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.57/0.60    inference(resolution,[],[f302,f195])).
% 1.57/0.60  fof(f195,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f194,f87])).
% 1.57/0.60  fof(f87,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f40])).
% 1.57/0.60  fof(f40,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.57/0.60    inference(flattening,[],[f39])).
% 1.57/0.60  fof(f39,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f12])).
% 1.57/0.60  fof(f12,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.57/0.60  fof(f194,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 1.57/0.60    inference(resolution,[],[f66,f48])).
% 1.57/0.60  fof(f66,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r2_hidden(X2,X3) | ~r1_xboole_0(X1,X3) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f32])).
% 1.57/0.60  fof(f32,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(flattening,[],[f31])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f17])).
% 1.57/0.60  fof(f17,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).
% 1.57/0.60  fof(f58,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f29])).
% 1.57/0.60  fof(f650,plain,(
% 1.57/0.60    ~v3_pre_topc(sK2,sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f646,f356])).
% 1.57/0.60  fof(f356,plain,(
% 1.57/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.60    inference(resolution,[],[f355,f41])).
% 1.57/0.60  fof(f41,plain,(
% 1.57/0.60    ~v1_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f646,plain,(
% 1.57/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0)),
% 1.57/0.60    inference(resolution,[],[f611,f357])).
% 1.57/0.60  fof(f357,plain,(
% 1.57/0.60    r1_xboole_0(sK1,sK2)),
% 1.57/0.60    inference(resolution,[],[f355,f44])).
% 1.57/0.60  fof(f44,plain,(
% 1.57/0.60    ~v1_tops_1(sK1,sK0) | r1_xboole_0(sK1,sK2)),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f611,plain,(
% 1.57/0.60    ( ! [X0] : (~r1_xboole_0(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) )),
% 1.57/0.60    inference(resolution,[],[f598,f351])).
% 1.57/0.60  fof(f351,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,X1)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f350,f84])).
% 1.57/0.60  fof(f350,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(sK1,X1)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f343,f46])).
% 1.57/0.60  fof(f343,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.57/0.60    inference(superposition,[],[f195,f342])).
% 1.57/0.60  fof(f598,plain,(
% 1.57/0.60    ( ! [X2] : (r2_hidden(sK4(sK0,k1_xboole_0,sK2),X2)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f595,f50])).
% 1.57/0.60  fof(f595,plain,(
% 1.57/0.60    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) | r2_hidden(sK4(sK0,k1_xboole_0,sK2),X2)) )),
% 1.57/0.60    inference(resolution,[],[f591,f84])).
% 1.57/0.60  fof(f591,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f590,f357])).
% 1.57/0.60  fof(f590,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0) | ~r1_xboole_0(sK1,sK2)),
% 1.57/0.60    inference(subsumption_resolution,[],[f589,f356])).
% 1.57/0.60  fof(f589,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2)),
% 1.57/0.60    inference(subsumption_resolution,[],[f570,f358])).
% 1.57/0.60  fof(f570,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2)),
% 1.57/0.60    inference(resolution,[],[f564,f351])).
% 1.57/0.60  fof(f564,plain,(
% 1.57/0.60    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) | r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f556,f359])).
% 1.57/0.60  fof(f359,plain,(
% 1.57/0.60    k1_xboole_0 != sK2),
% 1.57/0.60    inference(resolution,[],[f355,f42])).
% 1.57/0.60  fof(f42,plain,(
% 1.57/0.60    ~v1_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f556,plain,(
% 1.57/0.60    k1_xboole_0 = sK2 | r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) | r2_hidden(sK4(sK0,k1_xboole_0,sK2),k1_xboole_0)),
% 1.57/0.60    inference(resolution,[],[f552,f356])).
% 1.57/0.60  fof(f552,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f551])).
% 1.57/0.60  fof(f551,plain,(
% 1.57/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f550,f139])).
% 1.57/0.60  fof(f139,plain,(
% 1.57/0.60    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f138,f48])).
% 1.57/0.60  fof(f138,plain,(
% 1.57/0.60    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f134,f50])).
% 1.57/0.60  fof(f134,plain,(
% 1.57/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.57/0.60    inference(resolution,[],[f132,f57])).
% 1.57/0.60  fof(f57,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.57/0.60    inference(cnf_transformation,[],[f28])).
% 1.57/0.60  fof(f28,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(flattening,[],[f27])).
% 1.57/0.60  fof(f27,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f16])).
% 1.57/0.60  fof(f16,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.57/0.60  fof(f132,plain,(
% 1.57/0.60    v4_pre_topc(k1_xboole_0,sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f131,f50])).
% 1.57/0.60  fof(f131,plain,(
% 1.57/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f130,f106])).
% 1.57/0.60  fof(f106,plain,(
% 1.57/0.60    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 1.57/0.60    inference(forward_demodulation,[],[f105,f103])).
% 1.57/0.60  fof(f105,plain,(
% 1.57/0.60    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 1.57/0.60    inference(subsumption_resolution,[],[f104,f48])).
% 1.57/0.60  fof(f104,plain,(
% 1.57/0.60    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 1.57/0.60    inference(resolution,[],[f79,f47])).
% 1.57/0.60  fof(f47,plain,(
% 1.57/0.60    v2_pre_topc(sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f24])).
% 1.57/0.60  fof(f79,plain,(
% 1.57/0.60    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f36])).
% 1.57/0.60  fof(f36,plain,(
% 1.57/0.60    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.57/0.60    inference(flattening,[],[f35])).
% 1.57/0.60  fof(f35,plain,(
% 1.57/0.60    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f19])).
% 1.57/0.60  fof(f19,axiom,(
% 1.57/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.57/0.60  fof(f130,plain,(
% 1.57/0.60    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 1.57/0.60    inference(superposition,[],[f129,f124])).
% 1.57/0.60  fof(f124,plain,(
% 1.57/0.60    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(forward_demodulation,[],[f123,f100])).
% 1.57/0.60  fof(f100,plain,(
% 1.57/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(forward_demodulation,[],[f90,f89])).
% 1.57/0.60  fof(f89,plain,(
% 1.57/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f51,f81])).
% 1.57/0.60  fof(f81,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f11])).
% 1.57/0.60  fof(f11,axiom,(
% 1.57/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.57/0.60  fof(f51,plain,(
% 1.57/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.57/0.60  fof(f90,plain,(
% 1.57/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.57/0.60    inference(definition_unfolding,[],[f52,f88])).
% 1.57/0.60  fof(f88,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f82,f81])).
% 1.57/0.60  fof(f82,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f3])).
% 1.57/0.60  fof(f3,axiom,(
% 1.57/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.60  fof(f52,plain,(
% 1.57/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f5])).
% 1.57/0.60  fof(f5,axiom,(
% 1.57/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.60  fof(f123,plain,(
% 1.57/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f120,f89])).
% 1.57/0.60  fof(f120,plain,(
% 1.57/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(resolution,[],[f92,f50])).
% 1.57/0.60  fof(f92,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f83,f88])).
% 1.57/0.60  fof(f83,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f37])).
% 1.57/0.60  fof(f37,plain,(
% 1.57/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f7])).
% 1.57/0.60  fof(f7,axiom,(
% 1.57/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.57/0.60  fof(f129,plain,(
% 1.57/0.60    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.57/0.60    inference(resolution,[],[f60,f48])).
% 1.57/0.60  fof(f60,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f30])).
% 1.57/0.60  fof(f30,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f20])).
% 1.57/0.60  fof(f20,axiom,(
% 1.57/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.57/0.60  fof(f550,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | k2_pre_topc(sK0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f548,f50])).
% 1.57/0.60  fof(f548,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f547])).
% 1.57/0.60  fof(f547,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(resolution,[],[f545,f148])).
% 1.57/0.60  fof(f545,plain,(
% 1.57/0.60    ( ! [X0] : (~r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f544])).
% 1.57/0.60  fof(f544,plain,(
% 1.57/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f543,f139])).
% 1.57/0.60  fof(f543,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | k2_pre_topc(sK0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f541,f50])).
% 1.57/0.60  fof(f541,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f540])).
% 1.57/0.60  fof(f540,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK4(sK0,k1_xboole_0,X0),X0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0)) | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | r2_hidden(sK4(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(resolution,[],[f510,f184])).
% 1.57/0.60  fof(f184,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),sK6(sK0,k1_xboole_0,sK4(sK0,X0,X1))) | r2_hidden(sK4(sK0,X0,X1),k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f183,f148])).
% 1.57/0.60  fof(f183,plain,(
% 1.57/0.60    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f182,f48])).
% 1.57/0.60  fof(f182,plain,(
% 1.57/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f181,f50])).
% 1.57/0.60  fof(f181,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f180])).
% 1.57/0.60  fof(f180,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(superposition,[],[f96,f139])).
% 1.57/0.60  fof(f96,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | r2_hidden(X3,sK6(X0,X1,X3)) | r2_hidden(X3,k2_pre_topc(X0,X1))) )),
% 1.57/0.60    inference(equality_resolution,[],[f71])).
% 1.57/0.60  fof(f71,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_struct_0(X0)) | r2_hidden(X3,sK6(X0,X1,X3)) | r2_hidden(X3,X2) | k2_pre_topc(X0,X1) != X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f510,plain,(
% 1.57/0.60    ( ! [X10,X9] : (~r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X9 | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9) | ~r2_hidden(X10,u1_struct_0(sK0)) | r2_hidden(X10,k1_xboole_0)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f509,f139])).
% 1.57/0.60  fof(f509,plain,(
% 1.57/0.60    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10)) | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9) | k2_pre_topc(sK0,k1_xboole_0) = X9 | ~r2_hidden(X10,u1_struct_0(sK0)) | r2_hidden(X10,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f508,f191])).
% 1.57/0.60  fof(f191,plain,(
% 1.57/0.60    ( ! [X0] : (v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f190,f48])).
% 1.57/0.60  fof(f190,plain,(
% 1.57/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f189,f50])).
% 1.57/0.60  fof(f189,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f188])).
% 1.57/0.60  fof(f188,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | v3_pre_topc(sK6(sK0,k1_xboole_0,X0),sK0) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(superposition,[],[f97,f139])).
% 1.57/0.60  fof(f97,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | v3_pre_topc(sK6(X0,X1,X3),X0) | r2_hidden(X3,k2_pre_topc(X0,X1))) )),
% 1.57/0.60    inference(equality_resolution,[],[f70])).
% 1.57/0.60  fof(f70,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_struct_0(X0)) | v3_pre_topc(sK6(X0,X1,X3),X0) | r2_hidden(X3,X2) | k2_pre_topc(X0,X1) != X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f508,plain,(
% 1.57/0.60    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(sK0,k1_xboole_0,X10),sK0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10)) | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9) | k2_pre_topc(sK0,k1_xboole_0) = X9 | ~r2_hidden(X10,u1_struct_0(sK0)) | r2_hidden(X10,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f507,f238])).
% 1.57/0.60  fof(f238,plain,(
% 1.57/0.60    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f237,f48])).
% 1.57/0.60  fof(f237,plain,(
% 1.57/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f236,f50])).
% 1.57/0.60  fof(f236,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f235])).
% 1.57/0.60  fof(f235,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | m1_subset_1(sK6(sK0,k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(superposition,[],[f98,f139])).
% 1.57/0.60  fof(f98,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | m1_subset_1(sK6(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X3,k2_pre_topc(X0,X1))) )),
% 1.57/0.60    inference(equality_resolution,[],[f69])).
% 1.57/0.60  fof(f69,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_struct_0(X0)) | m1_subset_1(sK6(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X3,X2) | k2_pre_topc(X0,X1) != X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f507,plain,(
% 1.57/0.60    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK6(sK0,k1_xboole_0,X10),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(sK0,k1_xboole_0,X10),sK0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10)) | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9) | k2_pre_topc(sK0,k1_xboole_0) = X9 | ~r2_hidden(X10,u1_struct_0(sK0)) | r2_hidden(X10,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f500,f50])).
% 1.57/0.60  fof(f500,plain,(
% 1.57/0.60    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK6(sK0,k1_xboole_0,X10),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK6(sK0,k1_xboole_0,X10),sK0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X9),sK6(sK0,k1_xboole_0,X10)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X9),X9) | k2_pre_topc(sK0,k1_xboole_0) = X9 | ~r2_hidden(X10,u1_struct_0(sK0)) | r2_hidden(X10,k1_xboole_0)) )),
% 1.57/0.60    inference(resolution,[],[f432,f178])).
% 1.57/0.60  fof(f178,plain,(
% 1.57/0.60    ( ! [X0] : (r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f177,f48])).
% 1.57/0.60  fof(f177,plain,(
% 1.57/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f176,f50])).
% 1.57/0.60  fof(f176,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f175])).
% 1.57/0.60  fof(f175,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | r1_xboole_0(k1_xboole_0,sK6(sK0,k1_xboole_0,X0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(superposition,[],[f95,f139])).
% 1.57/0.60  fof(f95,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | r1_xboole_0(X1,sK6(X0,X1,X3)) | r2_hidden(X3,k2_pre_topc(X0,X1))) )),
% 1.57/0.60    inference(equality_resolution,[],[f72])).
% 1.57/0.60  fof(f72,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_struct_0(X0)) | r1_xboole_0(X1,sK6(X0,X1,X3)) | r2_hidden(X3,X2) | k2_pre_topc(X0,X1) != X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  fof(f432,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1) )),
% 1.57/0.60    inference(resolution,[],[f77,f48])).
% 1.57/0.60  fof(f77,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~r2_hidden(sK4(X0,X1,X2),X4) | ~r1_xboole_0(X1,X4) | r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.57/0.60    inference(cnf_transformation,[],[f34])).
% 1.57/0.60  % SZS output end Proof for theBenchmark
% 1.57/0.60  % (20192)------------------------------
% 1.57/0.60  % (20192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (20192)Termination reason: Refutation
% 1.57/0.60  
% 1.57/0.60  % (20192)Memory used [KB]: 6780
% 1.57/0.60  % (20192)Time elapsed: 0.189 s
% 1.57/0.60  % (20192)------------------------------
% 1.57/0.60  % (20192)------------------------------
% 1.57/0.61  % (20185)Success in time 0.233 s
%------------------------------------------------------------------------------
