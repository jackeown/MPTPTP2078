%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 318 expanded)
%              Number of leaves         :    5 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 (2344 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f950,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f22,f25,f24,f21,f23,f20,f94,f409,f41,f35,f16,f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f16,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f35,plain,(
    ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f18,plain,(
    ~ r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f38,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f38,plain,(
    m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f22,f23,f21,f25,f24,f20,f19,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f409,plain,(
    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f21,f24,f22,f25,f23,f20,f41,f34,f19,f26])).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) ),
    inference(unit_resulting_resolution,[],[f17,f92,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f21,f24,f22,f25,f23,f20,f41,f34,f19,f27])).

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
      | r2_hidden(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (1518)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (1518)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f950,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f22,f25,f24,f21,f23,f20,f94,f409,f41,f35,f16,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) & r1_tarski(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) & r1_tarski(X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X3) => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X3) => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f18,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ~r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f34,f38,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f22,f23,f21,f25,f24,f20,f19,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f18,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f409,plain,(
% 0.20/0.47    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f21,f24,f22,f25,f23,f20,f41,f34,f19,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f92,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f21,f24,f22,f25,f23,f20,f41,f34,f19,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    v4_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v5_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    l1_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v3_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (1518)------------------------------
% 0.20/0.47  % (1518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1518)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (1518)Memory used [KB]: 1918
% 0.20/0.47  % (1518)Time elapsed: 0.066 s
% 0.20/0.47  % (1518)------------------------------
% 0.20/0.47  % (1518)------------------------------
% 0.20/0.47  % (1502)Success in time 0.117 s
%------------------------------------------------------------------------------
