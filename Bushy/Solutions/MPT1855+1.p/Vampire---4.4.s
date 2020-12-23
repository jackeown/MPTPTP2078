%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t23_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:29 EDT 2019

% Result     : Theorem 16.01s
% Output     : Refutation 16.01s
% Verified   : 
% Statistics : Number of formulae       :  121 (2163 expanded)
%              Number of leaves         :   19 ( 618 expanded)
%              Depth                    :   26
%              Number of atoms          :  410 (11823 expanded)
%              Number of equality atoms :   74 (1691 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4021,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4020,f1163])).

fof(f1163,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(sK1)))) ),
    inference(subsumption_resolution,[],[f1161,f430])).

fof(f430,plain,(
    m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f413,f361])).

fof(f361,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f358,f97])).

fof(f97,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_pre_topc(sK1,sK0)
    & v7_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f77,f76])).

fof(f76,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_pre_topc(X1,sK0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK1,X0)
        & v7_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t23_tex_2)).

fof(f358,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f109,f100])).

fof(f100,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f78])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',l17_tex_2)).

fof(f413,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
      | m1_subset_1(sK4(sK1),X0) ) ),
    inference(resolution,[],[f412,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t4_subset)).

fof(f412,plain,(
    r2_hidden(sK4(sK1),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f411,f151])).

fof(f151,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f149,f100])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f108,f97])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_m1_pre_topc)).

fof(f411,plain,
    ( r2_hidden(sK4(sK1),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f410,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_l1_pre_topc)).

fof(f410,plain,
    ( ~ l1_struct_0(sK1)
    | r2_hidden(sK4(sK1),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f409,f98])).

fof(f98,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

fof(f409,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | r2_hidden(sK4(sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f376,f99])).

fof(f99,plain,(
    v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

fof(f376,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK4(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f375,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',fc2_struct_0)).

fof(f375,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(sK4(X0),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f114,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t2_subset)).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f84,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',d1_tex_1)).

fof(f1161,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(sK1))))
    | ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f101,f1032])).

fof(f1032,plain,(
    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK4(sK1))) ),
    inference(forward_demodulation,[],[f1031,f700])).

fof(f700,plain,(
    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    inference(subsumption_resolution,[],[f669,f692])).

fof(f692,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f685,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t7_boole)).

fof(f685,plain,(
    r2_hidden(sK4(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f678,f363])).

fof(f363,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f361,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t3_subset)).

fof(f678,plain,(
    ! [X1] :
      ( ~ r1_tarski(u1_struct_0(sK1),X1)
      | r2_hidden(sK4(sK1),X1) ) ),
    inference(superposition,[],[f132,f666])).

fof(f666,plain,(
    u1_struct_0(sK1) = k1_tarski(sK4(sK1)) ),
    inference(subsumption_resolution,[],[f665,f151])).

fof(f665,plain,
    ( u1_struct_0(sK1) = k1_tarski(sK4(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f664,f105])).

fof(f664,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_tarski(sK4(sK1)) ),
    inference(forward_demodulation,[],[f663,f426])).

fof(f426,plain,(
    k6_domain_1(u1_struct_0(sK1),sK4(sK1)) = k1_tarski(sK4(sK1)) ),
    inference(subsumption_resolution,[],[f424,f418])).

fof(f418,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f412,f137])).

fof(f424,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4(sK1)) = k1_tarski(sK4(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f416,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',redefinition_k6_domain_1)).

fof(f416,plain,(
    m1_subset_1(sK4(sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f412,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t1_subset)).

fof(f663,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK4(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f662,f98])).

fof(f662,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK4(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f115,f99])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK4(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t37_zfmisc_1)).

fof(f669,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f666,f432])).

fof(f432,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4(sK1)) = k1_tarski(sK4(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f430,f130])).

fof(f1031,plain,(
    u1_struct_0(k1_tex_2(sK0,sK4(sK1))) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    inference(subsumption_resolution,[],[f1030,f96])).

fof(f96,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

fof(f1030,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK4(sK1))) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1011,f97])).

fof(f1011,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK4(sK1))) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f145,f430])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f144,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_k1_tex_2)).

fof(f144,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f143,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f143,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f142,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f142,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',d4_tex_2)).

fof(f101,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f4020,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(sK1)))) ),
    inference(forward_demodulation,[],[f4019,f1032])).

fof(f4019,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(sK1))),u1_pre_topc(k1_tex_2(sK0,sK4(sK1)))) ),
    inference(subsumption_resolution,[],[f4013,f1032])).

fof(f4013,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK4(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(sK1))),u1_pre_topc(k1_tex_2(sK0,sK4(sK1)))) ),
    inference(resolution,[],[f1243,f624])).

fof(f624,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK4(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f623,f96])).

fof(f623,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK4(sK1)),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f612,f97])).

fof(f612,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK4(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f430])).

fof(f1243,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(sK1) != u1_struct_0(X0)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(subsumption_resolution,[],[f1235,f97])).

fof(f1235,plain,(
    ! [X0] :
      ( u1_struct_0(sK1) != u1_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f110,f100])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t5_tsep_1)).
%------------------------------------------------------------------------------
