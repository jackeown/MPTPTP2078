%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1854+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 109 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 483 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30671)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_6 on theBenchmark
fof(f5507,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5506,f3946])).

fof(f3946,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3834])).

fof(f3834,plain,
    ( v7_struct_0(sK4)
    & v1_tex_2(k1_tex_2(sK4,sK5),sK4)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3640,f3833,f3832])).

fof(f3832,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v7_struct_0(X0)
            & v1_tex_2(k1_tex_2(X0,X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v7_struct_0(sK4)
          & v1_tex_2(k1_tex_2(sK4,X1),sK4)
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3833,plain,
    ( ? [X1] :
        ( v7_struct_0(sK4)
        & v1_tex_2(k1_tex_2(sK4,X1),sK4)
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( v7_struct_0(sK4)
      & v1_tex_2(k1_tex_2(sK4,sK5),sK4)
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f3640,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3639])).

fof(f3639,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3619])).

fof(f3619,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ ( v7_struct_0(X0)
                & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f3618])).

fof(f3618,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tex_2)).

fof(f5506,plain,(
    ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f5498,f4046])).

fof(f4046,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3698])).

fof(f3698,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f5498,plain,(
    ~ l1_struct_0(sK4) ),
    inference(resolution,[],[f5492,f4277])).

fof(f4277,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(resolution,[],[f3945,f4045])).

fof(f4045,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3697])).

fof(f3697,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3696])).

fof(f3696,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3945,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3834])).

fof(f5492,plain,(
    v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f5491,f3947])).

fof(f3947,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f3834])).

fof(f5491,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f5485,f5248])).

fof(f5248,plain,(
    v1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f5247,f3946])).

fof(f5247,plain,
    ( v1_zfmisc_1(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f4461,f4046])).

fof(f4461,plain,
    ( ~ l1_struct_0(sK4)
    | v1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(resolution,[],[f3949,f3974])).

fof(f3974,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3642])).

fof(f3642,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f3641])).

fof(f3641,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1804])).

fof(f1804,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f3949,plain,(
    v7_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3834])).

fof(f5485,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f4515,f4205])).

fof(f4205,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3820])).

fof(f3820,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3819])).

fof(f3819,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3622])).

fof(f3622,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f4515,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f4514,f3945])).

fof(f4514,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f4513,f3946])).

fof(f4513,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f4506,f3947])).

fof(f4506,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f3948,f4012])).

fof(f4012,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3857])).

fof(f3857,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
              | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3680])).

fof(f3680,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3679])).

fof(f3679,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3617])).

fof(f3617,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f3948,plain,(
    v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f3834])).
%------------------------------------------------------------------------------
