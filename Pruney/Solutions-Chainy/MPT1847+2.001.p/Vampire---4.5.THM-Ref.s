%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 (3275 expanded)
%              Number of leaves         :   12 ( 584 expanded)
%              Depth                    :   27
%              Number of atoms          :  281 (14404 expanded)
%              Number of equality atoms :   59 (2460 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(subsumption_resolution,[],[f350,f168])).

fof(f168,plain,(
    ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f85,f164])).

fof(f164,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f85])).

fof(f160,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f82,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f82,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f79,f81])).

fof(f81,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f38,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(f80,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f78,plain,
    ( m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f84,f81])).

fof(f84,plain,(
    ~ v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f83,f38])).

fof(f83,plain,
    ( ~ v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f350,plain,(
    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f349,f333])).

fof(f333,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f331,f108])).

fof(f108,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f105,f40])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f39,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f39,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f331,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(resolution,[],[f330,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f330,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f329,f175])).

fof(f175,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f161,f164])).

fof(f161,plain,(
    u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f156,f40])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2))) ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f329,plain,(
    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f314,f107])).

fof(f107,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f314,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK1)) ),
    inference(resolution,[],[f257,f63])).

fof(f257,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f184,f249])).

fof(f249,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = k1_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f248,f226])).

fof(f226,plain,(
    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f213,f40])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f177,f50])).

fof(f177,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0) ),
    inference(backward_demodulation,[],[f163,f164])).

fof(f163,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2)),sK0) ),
    inference(subsumption_resolution,[],[f158,f40])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2)),sK0) ),
    inference(resolution,[],[f82,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f248,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = k1_pre_topc(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f205,f244])).

fof(f244,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f243,f175])).

fof(f243,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f238,f175])).

fof(f238,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))) ),
    inference(resolution,[],[f185,f177])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(X0) != u1_struct_0(sK0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f169,f165])).

fof(f165,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f36,f164])).

fof(f36,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f169,plain,(
    ! [X0] :
      ( u1_struct_0(X0) != u1_struct_0(sK0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(backward_demodulation,[],[f87,f164])).

fof(f87,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(X0) != u1_struct_0(sK2) ) ),
    inference(forward_demodulation,[],[f86,f36])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(X0) != u1_struct_0(sK2)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(X0) != u1_struct_0(sK2)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X1) != u1_struct_0(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

fof(f205,plain,
    ( k1_pre_topc(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))))
    | ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f204,f175])).

fof(f204,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | k1_pre_topc(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))) ),
    inference(resolution,[],[f176,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f176,plain,(
    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f162,f164])).

fof(f162,plain,(
    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f157,f40])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2))) ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f184,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)),sK1) ),
    inference(backward_demodulation,[],[f155,f165])).

fof(f155,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f148,f107])).

fof(f148,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(resolution,[],[f109,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f109,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f107,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f349,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f334,f167])).

fof(f167,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f82,f164])).

fof(f334,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f97,f333])).

fof(f97,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f37,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:30:09 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (5889)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (5894)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (5897)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (5884)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (5889)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f350,f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ~v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f85,f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    u1_struct_0(sK2) = u1_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f160,f85])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    u1_struct_0(sK2) = u1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f82,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f79,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f80,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~v1_tex_2(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f16])).
% 0.22/0.50  fof(f16,conjecture,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f71,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0)),
% 0.22/0.50    inference(resolution,[],[f35,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f78,f38])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(sK2,sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f70,f40])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(sK2,sK0)),
% 0.22/0.50    inference(resolution,[],[f35,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.22/0.50    inference(forward_demodulation,[],[f84,f81])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f38])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f72,f40])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0)),
% 0.22/0.51    inference(resolution,[],[f35,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.51    inference(forward_demodulation,[],[f349,f333])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f331,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f40])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(resolution,[],[f39,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f330,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f329,f175])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f161,f164])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f40])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK2)))),
% 0.22/0.51    inference(resolution,[],[f82,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f40])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.22/0.51    inference(resolution,[],[f39,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | r1_tarski(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_struct_0(sK1))),
% 0.22/0.51    inference(resolution,[],[f257,f63])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f184,f249])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = k1_pre_topc(sK0,u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f248,f226])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f213,f40])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f177,f50])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f163,f164])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2)),sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f40])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2)),sK0)),
% 0.22/0.51    inference(resolution,[],[f82,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = k1_pre_topc(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f205,f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))))),
% 0.22/0.51    inference(forward_demodulation,[],[f243,f175])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))))),
% 0.22/0.51    inference(subsumption_resolution,[],[f238,f175])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    u1_struct_0(sK0) != u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))))),
% 0.22/0.51    inference(resolution,[],[f185,f177])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(X0) != u1_struct_0(sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f169,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f36,f164])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X0] : (u1_struct_0(X0) != u1_struct_0(sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f87,f164])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) != u1_struct_0(sK2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f86,f36])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(X0) != u1_struct_0(sK2) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f73,f40])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) != u1_struct_0(sK2) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )),
% 0.22/0.51    inference(resolution,[],[f35,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | u1_struct_0(X1) != u1_struct_0(X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (u1_struct_0(X1) = u1_struct_0(X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    k1_pre_topc(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))) | ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f204,f175])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) | k1_pre_topc(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))),u1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))))),
% 0.22/0.51    inference(resolution,[],[f176,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f162,f164])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f40])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK2)))),
% 0.22/0.51    inference(resolution,[],[f82,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)),sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f155,f165])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f107])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 0.22/0.51    inference(resolution,[],[f109,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK1)),
% 0.22/0.51    inference(resolution,[],[f107,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f334,f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f82,f164])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(backward_demodulation,[],[f97,f333])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f96,f40])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f95,f39])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f37,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    v1_tex_2(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (5889)------------------------------
% 0.22/0.51  % (5889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5889)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (5889)Memory used [KB]: 6268
% 0.22/0.51  % (5889)Time elapsed: 0.089 s
% 0.22/0.51  % (5889)------------------------------
% 0.22/0.51  % (5889)------------------------------
% 0.22/0.51  % (5883)Success in time 0.143 s
%------------------------------------------------------------------------------
