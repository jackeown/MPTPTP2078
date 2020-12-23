%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  166 (4636 expanded)
%              Number of leaves         :   14 ( 833 expanded)
%              Depth                    :   50
%              Number of atoms          :  564 (18883 expanded)
%              Number of equality atoms :   47 ( 496 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(subsumption_resolution,[],[f381,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f381,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f380,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f380,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f379,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f379,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f377,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f377,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f372,f293])).

fof(f293,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f268,f282])).

fof(f282,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f281,f125])).

fof(f125,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f103,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f102,f44])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f42,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f281,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f280,f46])).

fof(f280,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f279,f101])).

fof(f101,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f42,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f279,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f278,f54])).

fof(f278,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f277,f44])).

fof(f277,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f276,f46])).

fof(f276,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f275,f103])).

fof(f275,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f274,f44])).

fof(f274,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f229,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f229,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(backward_demodulation,[],[f207,f216])).

fof(f216,plain,(
    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f215,f125])).

fof(f215,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f214,f46])).

fof(f214,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f213,f101])).

fof(f213,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f212,f54])).

fof(f212,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f211,f44])).

fof(f211,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f210,f46])).

fof(f210,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f209,f103])).

fof(f209,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f208,f44])).

fof(f208,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f201,f48])).

fof(f201,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f200,f158])).

fof(f158,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f157,f42])).

fof(f157,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f155,f43])).

fof(f155,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(f154,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f152,f147])).

fof(f147,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f146,f103])).

fof(f146,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f143,f44])).

fof(f143,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f41,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f152,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f151,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f151,plain,
    ( ~ v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f150,f103])).

fof(f150,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f145,f44])).

fof(f145,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f200,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f199,f43])).

fof(f199,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f188,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ v1_xboole_0(X1)
           => ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tex_2)).

fof(f188,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f180,f154])).

fof(f180,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f179,f103])).

fof(f179,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f178,f44])).

fof(f178,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f141,f48])).

fof(f141,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f140,f103])).

fof(f140,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f139,f44])).

fof(f139,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f207,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f206,f177])).

fof(f177,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f176,f42])).

fof(f176,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f174,f43])).

fof(f174,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f149,f53])).

fof(f149,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f148,f103])).

fof(f148,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f144,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f206,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f205,f43])).

fof(f205,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f186,f56])).

fof(f186,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f180,f149])).

fof(f268,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f267,f44])).

fof(f267,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f266,f46])).

fof(f266,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f265,f103])).

fof(f265,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f264,f44])).

fof(f264,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f228,f48])).

fof(f228,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(backward_demodulation,[],[f204,f216])).

fof(f204,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f203,f167])).

fof(f167,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f166,f42])).

fof(f166,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f164,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f147,f53])).

fof(f203,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f202,f43])).

fof(f202,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f187,f56])).

fof(f187,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f180,f147])).

fof(f372,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f367,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f367,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f366,f44])).

fof(f366,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f349,f46])).

fof(f349,plain,
    ( ~ l1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f348,f285])).

fof(f285,plain,
    ( ~ v7_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f193,f282])).

fof(f193,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f192,f42])).

fof(f192,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f189,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v7_struct_0(sK0) ),
    inference(resolution,[],[f180,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f348,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f347,f336])).

fof(f336,plain,(
    v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f335,f125])).

fof(f335,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f326,f46])).

fof(f326,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f309,f105])).

fof(f105,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f44])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f97,f43])).

fof(f97,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f42,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f309,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(superposition,[],[f57,f282])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f347,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f345,f42])).

fof(f345,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f337,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f337,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f297,f222])).

fof(f222,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK0) ),
    inference(backward_demodulation,[],[f169,f216])).

fof(f169,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f44])).

fof(f168,plain,
    ( v7_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f167,f46])).

fof(f297,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f296,f67])).

fof(f296,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f283,f282])).

fof(f283,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f141,f282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:02:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (11139)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.43  % (11131)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.43  % (11139)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f382,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f381,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    l1_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f14])).
% 0.22/0.44  fof(f14,conjecture,(
% 0.22/0.44    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.22/0.44  fof(f381,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0)),
% 0.22/0.44    inference(resolution,[],[f380,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.44  fof(f380,plain,(
% 0.22/0.44    ~l1_struct_0(sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f379,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ~v2_struct_0(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f379,plain,(
% 0.22/0.44    v2_struct_0(sK0) | ~l1_struct_0(sK0)),
% 0.22/0.44    inference(resolution,[],[f377,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.44  fof(f377,plain,(
% 0.22/0.44    v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f372,f293])).
% 0.22/0.44  fof(f293,plain,(
% 0.22/0.44    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.44    inference(backward_demodulation,[],[f268,f282])).
% 0.22/0.44  fof(f282,plain,(
% 0.22/0.44    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f281,f125])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f124,f44])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f103,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f102,f44])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f95,f43])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(resolution,[],[f42,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f281,plain,(
% 0.22/0.44    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f280,f46])).
% 0.22/0.44  fof(f280,plain,(
% 0.22/0.44    ~l1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f279,f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f100,f44])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f93,f43])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f42,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f37])).
% 0.22/0.44  fof(f279,plain,(
% 0.22/0.44    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f278,f54])).
% 0.22/0.44  fof(f278,plain,(
% 0.22/0.44    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f277,f44])).
% 0.22/0.44  fof(f277,plain,(
% 0.22/0.44    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.44    inference(resolution,[],[f276,f46])).
% 0.22/0.44  fof(f276,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f275,f103])).
% 0.22/0.44  fof(f275,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f274,f44])).
% 0.22/0.44  fof(f274,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(resolution,[],[f229,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.44  fof(f229,plain,(
% 0.22/0.44    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(backward_demodulation,[],[f207,f216])).
% 0.22/0.44  fof(f216,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f215,f125])).
% 0.22/0.44  fof(f215,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f214,f46])).
% 0.22/0.44  fof(f214,plain,(
% 0.22/0.44    ~l1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f213,f101])).
% 0.22/0.44  fof(f213,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f212,f54])).
% 0.22/0.44  fof(f212,plain,(
% 0.22/0.44    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f211,f44])).
% 0.22/0.44  fof(f211,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.44    inference(resolution,[],[f210,f46])).
% 0.22/0.44  fof(f210,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f209,f103])).
% 0.22/0.44  fof(f209,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f208,f44])).
% 0.22/0.44  fof(f208,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(resolution,[],[f201,f48])).
% 0.22/0.44  fof(f201,plain,(
% 0.22/0.44    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f200,f158])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | v7_struct_0(sK0) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f157,f42])).
% 0.22/0.44  fof(f157,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f155,f43])).
% 0.22/0.44  fof(f155,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f154,f53])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).
% 0.22/0.44  fof(f154,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f152,f147])).
% 0.22/0.44  fof(f147,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f146,f103])).
% 0.22/0.44  fof(f146,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f143,f44])).
% 0.22/0.44  fof(f143,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(resolution,[],[f41,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f152,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f151,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.44  fof(f151,plain,(
% 0.22/0.44    ~v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f150,f103])).
% 0.22/0.44  fof(f150,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f145,f44])).
% 0.22/0.44  fof(f145,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f41,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f200,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f199,f43])).
% 0.22/0.44  fof(f199,plain,(
% 0.22/0.44    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(resolution,[],[f188,f56])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~v1_xboole_0(X1) => (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tex_2)).
% 0.22/0.44  fof(f188,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f180,f154])).
% 0.22/0.44  fof(f180,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f179,f103])).
% 0.22/0.44  fof(f179,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f178,f44])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(resolution,[],[f141,f48])).
% 0.22/0.44  fof(f141,plain,(
% 0.22/0.44    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f140,f103])).
% 0.22/0.44  fof(f140,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f139,f44])).
% 0.22/0.44  fof(f139,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f40,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.22/0.44    inference(equality_resolution,[],[f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f207,plain,(
% 0.22/0.44    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f206,f177])).
% 0.22/0.44  fof(f177,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | v7_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f176,f42])).
% 0.22/0.44  fof(f176,plain,(
% 0.22/0.44    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f174,f43])).
% 0.22/0.44  fof(f174,plain,(
% 0.22/0.44    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f149,f53])).
% 0.22/0.44  fof(f149,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f148,f103])).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f144,f44])).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f41,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f206,plain,(
% 0.22/0.44    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f205,f43])).
% 0.22/0.44  fof(f205,plain,(
% 0.22/0.44    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(resolution,[],[f186,f56])).
% 0.22/0.44  fof(f186,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f180,f149])).
% 0.22/0.44  fof(f268,plain,(
% 0.22/0.44    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f267,f44])).
% 0.22/0.44  fof(f267,plain,(
% 0.22/0.44    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.44    inference(resolution,[],[f266,f46])).
% 0.22/0.44  fof(f266,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f265,f103])).
% 0.22/0.44  fof(f265,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f264,f44])).
% 0.22/0.44  fof(f264,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.44    inference(resolution,[],[f228,f48])).
% 0.22/0.44  fof(f228,plain,(
% 0.22/0.44    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(backward_demodulation,[],[f204,f216])).
% 0.22/0.44  fof(f204,plain,(
% 0.22/0.44    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f203,f167])).
% 0.22/0.44  fof(f167,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | v7_struct_0(sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f166,f42])).
% 0.22/0.44  fof(f166,plain,(
% 0.22/0.44    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f164,f43])).
% 0.22/0.44  fof(f164,plain,(
% 0.22/0.44    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f147,f53])).
% 0.22/0.44  fof(f203,plain,(
% 0.22/0.44    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f202,f43])).
% 0.22/0.44  fof(f202,plain,(
% 0.22/0.44    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.44    inference(resolution,[],[f187,f56])).
% 0.22/0.44  fof(f187,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(resolution,[],[f180,f147])).
% 0.22/0.44  fof(f372,plain,(
% 0.22/0.44    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(resolution,[],[f367,f67])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.22/0.44    inference(equality_resolution,[],[f59])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f35])).
% 0.22/0.44  fof(f367,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f366,f44])).
% 0.22/0.44  fof(f366,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.44    inference(resolution,[],[f349,f46])).
% 0.22/0.44  fof(f349,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.44    inference(resolution,[],[f348,f285])).
% 0.22/0.44  fof(f285,plain,(
% 0.22/0.44    ~v7_struct_0(sK0) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.44    inference(backward_demodulation,[],[f193,f282])).
% 0.22/0.44  fof(f193,plain,(
% 0.22/0.44    ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f192,f42])).
% 0.22/0.44  fof(f192,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v7_struct_0(sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f189,f43])).
% 0.22/0.44  fof(f189,plain,(
% 0.22/0.44    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v7_struct_0(sK0)),
% 0.22/0.44    inference(resolution,[],[f180,f55])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.22/0.44  fof(f348,plain,(
% 0.22/0.44    v7_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f347,f336])).
% 0.22/0.44  fof(f336,plain,(
% 0.22/0.44    v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f335,f125])).
% 0.22/0.44  fof(f335,plain,(
% 0.22/0.44    v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f326,f46])).
% 0.22/0.44  fof(f326,plain,(
% 0.22/0.44    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f309,f105])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f104,f44])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0) | v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(subsumption_resolution,[],[f97,f43])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f42,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.44  fof(f309,plain,(
% 0.22/0.44    v1_zfmisc_1(u1_struct_0(sK0)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.44    inference(superposition,[],[f57,f282])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.45  fof(f347,plain,(
% 0.22/0.45    v7_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f345,f42])).
% 0.22/0.45  fof(f345,plain,(
% 0.22/0.45    v7_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.45    inference(resolution,[],[f337,f45])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~v1_zfmisc_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.45  fof(f337,plain,(
% 0.22/0.45    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v7_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f297,f222])).
% 0.22/0.45  fof(f222,plain,(
% 0.22/0.45    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v7_struct_0(sK0)),
% 0.22/0.45    inference(backward_demodulation,[],[f169,f216])).
% 0.22/0.45  fof(f169,plain,(
% 0.22/0.45    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v7_struct_0(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f168,f44])).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    v7_struct_0(sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.45    inference(resolution,[],[f167,f46])).
% 0.22/0.45  fof(f297,plain,(
% 0.22/0.45    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f296,f67])).
% 0.22/0.45  fof(f296,plain,(
% 0.22/0.45    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.45    inference(forward_demodulation,[],[f283,f282])).
% 0.22/0.45  fof(f283,plain,(
% 0.22/0.45    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.45    inference(backward_demodulation,[],[f141,f282])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (11139)------------------------------
% 0.22/0.45  % (11139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (11139)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (11139)Memory used [KB]: 1663
% 0.22/0.45  % (11139)Time elapsed: 0.032 s
% 0.22/0.45  % (11139)------------------------------
% 0.22/0.45  % (11139)------------------------------
% 0.22/0.45  % (11125)Success in time 0.085 s
%------------------------------------------------------------------------------
