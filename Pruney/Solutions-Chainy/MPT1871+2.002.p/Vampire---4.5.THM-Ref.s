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
% DateTime   : Thu Dec  3 13:21:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 445 expanded)
%              Number of leaves         :    4 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  215 (3770 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f72])).

fof(f72,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f15,f21,f20,f62,f25])).

fof(f25,plain,(
    ! [X4,X0,X3] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v4_pre_topc(X4,X0)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v4_pre_topc(X4,X0)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X4,X0)
                    & v2_tex_2(X3,X0)
                    & v4_pre_topc(X4,X0)
                    & v4_pre_topc(X3,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tex_2)).

fof(f62,plain,(
    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f23,f40,f41,f42,f55,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

fof(f55,plain,(
    m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f29])).

fof(f29,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f26])).

fof(f26,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    v4_pre_topc(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f28])).

fof(f28,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    v4_pre_topc(sK4(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f27])).

fof(f27,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  & v2_tex_2(X1,X0)
                  & v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tex_2)).

fof(f20,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f23,f40,f41,f42,f55,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_1)).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (22510)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.46  % (22521)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (22521)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f15,f21,f20,f62,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~v4_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X3] : (! [X4] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | ~v2_tex_2(X4,X0) | ~v2_tex_2(X3,X0) | ~v4_pre_topc(X4,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X1] : (? [X2] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : ((! [X3] : (! [X4] : ((v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | (~v2_tex_2(X4,X0) | ~v2_tex_2(X3,X0) | ~v4_pre_topc(X4,X0) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X1] : (? [X2] : (((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => (v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0))))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X4,X0) & v2_tex_2(X3,X0) & v4_pre_topc(X4,X0) & v4_pre_topc(X3,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0))))))),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => (v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0))))) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tex_2)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f23,f40,f41,f42,f55,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v4_pre_topc(X2,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~v4_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~v4_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v4_pre_topc(sK3(sK0),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK3(X0),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~v4_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v4_pre_topc(sK4(sK0),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f19,f18,f17,f16,f21,f15,f20,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK4(X0),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~v4_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tex_2)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v4_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v2_tex_2(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v4_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f23,f40,f41,f42,f55,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v4_pre_topc(X2,X0) | v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22521)------------------------------
% 0.21/0.48  % (22521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22521)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22521)Memory used [KB]: 1023
% 0.21/0.48  % (22521)Time elapsed: 0.059 s
% 0.21/0.48  % (22521)------------------------------
% 0.21/0.48  % (22521)------------------------------
% 0.21/0.48  % (22505)Success in time 0.121 s
%------------------------------------------------------------------------------
