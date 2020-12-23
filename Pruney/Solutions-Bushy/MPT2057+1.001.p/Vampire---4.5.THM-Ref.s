%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2057+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 626 expanded)
%              Number of leaves         :   10 ( 112 expanded)
%              Depth                    :   50
%              Number of atoms          :  541 (4480 expanded)
%              Number of equality atoms :   36 (  74 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(subsumption_resolution,[],[f169,f35])).

fof(f35,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f169,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f27,f166])).

fof(f166,plain,(
    o_0_0_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f165,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X2,X1)
                <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
             => ( r2_hidden(X2,X1)
              <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow19)).

fof(f165,plain,
    ( o_0_0_xboole_0 = sK2
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f34])).

fof(f34,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f164,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f163,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f163,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f162,f34])).

fof(f162,plain,
    ( o_0_0_xboole_0 = sK2
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f161,f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f161,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | o_0_0_xboole_0 = sK2
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f160,f33])).

fof(f160,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f14])).

fof(f159,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f31,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f158,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f30])).

fof(f30,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f157,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f156,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f34])).

fof(f155,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f153,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f153,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f152,f120])).

fof(f120,plain,(
    ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(resolution,[],[f119,f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,(
    r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f118,plain,
    ( r2_hidden(sK2,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,
    ( r2_hidden(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f116,f38])).

fof(f116,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f115,f34])).

fof(f115,plain,
    ( r2_hidden(sK2,sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f114,f37])).

fof(f114,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,sK1)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f113,f33])).

fof(f113,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f112,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f111,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f30])).

fof(f110,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f29])).

fof(f109,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f108,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f100,f44])).

fof(f100,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f94,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f94,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_hidden(sK2,sK1) ),
    inference(backward_demodulation,[],[f67,f91])).

fof(f91,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(forward_demodulation,[],[f90,f52])).

fof(f52,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X1) = k4_xboole_0(sK1,X1) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f90,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f89,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f87,f30])).

fof(f87,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(resolution,[],[f86,f31])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(o_0_0_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(o_0_0_xboole_0)) ) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(o_0_0_xboole_0)) ) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f36,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f67,plain,
    ( r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f66,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f65,f25])).

fof(f25,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f64,f34])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f62,f32])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f61,f30])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f60,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X0)
      | v2_struct_0(k3_yellow19(sK0,X0,X1))
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,k2_yellow19(sK0,k3_yellow19(sK0,X0,X1))) ) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X0)
      | v2_struct_0(k3_yellow19(sK0,X0,X1))
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,k2_yellow19(sK0,k3_yellow19(sK0,X0,X1))) ) ),
    inference(subsumption_resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X0)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(k3_yellow19(sK0,X0,X1))
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,k3_yellow19(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,k2_yellow19(sK0,k3_yellow19(sK0,X0,X1))) ) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) ) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f152,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2 ),
    inference(resolution,[],[f151,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(X0)))
      | sK2 = X0 ) ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f150,f34])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f144,f37])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f143,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f142,f31])).

fof(f142,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f141,f30])).

fof(f141,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f140,f29])).

fof(f140,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r2_hidden(X0,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f106,f56])).

fof(f106,plain,(
    ! [X1] :
      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r2_hidden(X1,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) ) ),
    inference(subsumption_resolution,[],[f105,f33])).

fof(f105,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f34])).

fof(f102,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f40,f91])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
