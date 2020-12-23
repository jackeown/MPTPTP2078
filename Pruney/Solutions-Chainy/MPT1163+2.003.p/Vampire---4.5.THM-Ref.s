%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 672 expanded)
%              Number of leaves         :    6 ( 135 expanded)
%              Depth                    :    9
%              Number of atoms          :  199 (5274 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23,f26,f25,f22,f24,f21,f92,f244,f51,f53,f17,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f17,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( r1_tarski(X2,X3)
                     => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

fof(f53,plain,(
    ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f19,f46,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f46,plain,(
    m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f23,f24,f22,f26,f25,f21,f20,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ~ r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f23,f24,f22,f26,f25,f21,f17,f36])).

fof(f51,plain,(
    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f45,f19,f46,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f244,plain,(
    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f25,f23,f26,f24,f21,f51,f52,f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f19,f46,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) ),
    inference(unit_resulting_resolution,[],[f37,f90,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f90,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f22,f25,f23,f26,f24,f21,f51,f52,f20,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f18,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f18,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (23643)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.44  % (23643)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f437,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f23,f26,f25,f22,f24,f21,f92,f244,f51,f53,f17,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) & r1_tarski(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) & r1_tarski(X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X3) => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)))))))),
% 0.20/0.44    inference(negated_conjecture,[],[f6])).
% 0.20/0.44  fof(f6,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X3) => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f45,f19,f46,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f23,f24,f22,f26,f25,f21,f20,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ~r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f23,f24,f22,f26,f25,f21,f17,f36])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f45,f19,f46,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f244,plain,(
% 0.20/0.44    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f22,f25,f23,f26,f24,f21,f51,f52,f20,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f45,f19,f46,f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f37,f90,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f22,f25,f23,f26,f24,f21,f51,f52,f20,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(sK3))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f18,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    r1_tarski(sK2,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    v4_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ~v2_struct_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    v5_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    l1_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    v3_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (23643)------------------------------
% 0.20/0.44  % (23643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23643)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (23643)Memory used [KB]: 1407
% 0.20/0.44  % (23643)Time elapsed: 0.022 s
% 0.20/0.44  % (23643)------------------------------
% 0.20/0.44  % (23643)------------------------------
% 0.20/0.45  % (23627)Success in time 0.087 s
%------------------------------------------------------------------------------
