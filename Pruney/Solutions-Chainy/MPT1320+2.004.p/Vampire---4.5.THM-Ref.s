%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:52 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 183 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 790 expanded)
%              Number of equality atoms :   16 (  47 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1404,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1371,f1369,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ sP9(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1369,plain,(
    sP9(sK7(k3_xboole_0(sK1,sK2),sK2),sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f1361,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP9(sK7(k3_xboole_0(X0,X1),X2),X1,X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP9(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1361,plain,(
    ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f1359,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1359,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) ),
    inference(forward_demodulation,[],[f1345,f250])).

fof(f250,plain,(
    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f26,f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f1345,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f26,f419,f167,f24,f21,f408])).

fof(f408,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP5(X3,X2,X0,X1)
      | r2_hidden(X3,k1_tops_2(X1,X0,X2)) ) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP5(X3,X2,X0,X1)
      | r2_hidden(X3,k1_tops_2(X1,X0,X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f167,plain,(
    ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f23,f156])).

fof(f156,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f24,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f23,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f419,plain,(
    sP5(k3_xboole_0(sK1,sK2),sK3,sK2,sK0) ),
    inference(superposition,[],[f275,f156])).

fof(f275,plain,(
    ! [X0] : sP5(k9_subset_1(u1_struct_0(sK0),sK1,X0),sK3,X0,sK0) ),
    inference(unit_resulting_resolution,[],[f22,f25,f54])).

fof(f54,plain,(
    ! [X2,X0,X5,X1] :
      ( sP5(k9_subset_1(u1_struct_0(X0),X5,X1),X2,X1,X0)
      | ~ r2_hidden(X5,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | k9_subset_1(u1_struct_0(X0),X5,X1) != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f1371,plain,(
    ~ r2_hidden(sK7(k3_xboole_0(sK1,sK2),sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f1361,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (11596)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (11588)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (11580)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (11579)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (11578)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11581)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (11577)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11576)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11602)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (11587)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11590)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (11582)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (11589)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (11593)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (11573)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11601)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (11594)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (11600)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (11595)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (11574)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (11592)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (11585)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (11597)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (11591)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (11586)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.55  % (11584)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (11598)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.55  % (11575)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.47/0.56  % (11590)Refutation not found, incomplete strategy% (11590)------------------------------
% 1.47/0.56  % (11590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (11590)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (11590)Memory used [KB]: 10746
% 1.47/0.56  % (11590)Time elapsed: 0.154 s
% 1.47/0.56  % (11590)------------------------------
% 1.47/0.56  % (11590)------------------------------
% 1.47/0.56  % (11583)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.59  % (11599)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.27/0.70  % (11597)Refutation found. Thanks to Tanya!
% 2.27/0.70  % SZS status Theorem for theBenchmark
% 2.27/0.70  % SZS output start Proof for theBenchmark
% 2.27/0.70  fof(f1404,plain,(
% 2.27/0.70    $false),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f1371,f1369,f47])).
% 2.27/0.70  fof(f47,plain,(
% 2.27/0.70    ( ! [X0,X3,X1] : (~sP9(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f2])).
% 2.27/0.70  fof(f2,axiom,(
% 2.27/0.70    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.27/0.70  fof(f1369,plain,(
% 2.27/0.70    sP9(sK7(k3_xboole_0(sK1,sK2),sK2),sK2,sK1)),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f1361,f85])).
% 2.27/0.70  fof(f85,plain,(
% 2.27/0.70    ( ! [X2,X0,X1] : (sP9(sK7(k3_xboole_0(X0,X1),X2),X1,X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.27/0.70    inference(resolution,[],[f55,f38])).
% 2.27/0.70  fof(f38,plain,(
% 2.27/0.70    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f15])).
% 2.27/0.70  fof(f15,plain,(
% 2.27/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f1])).
% 2.27/0.70  fof(f1,axiom,(
% 2.27/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.27/0.70  fof(f55,plain,(
% 2.27/0.70    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | sP9(X3,X1,X0)) )),
% 2.27/0.70    inference(equality_resolution,[],[f49])).
% 2.27/0.70  fof(f49,plain,(
% 2.27/0.70    ( ! [X2,X0,X3,X1] : (sP9(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.27/0.70    inference(cnf_transformation,[],[f2])).
% 2.27/0.70  fof(f1361,plain,(
% 2.27/0.70    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2)),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f1359,f40])).
% 2.27/0.70  fof(f40,plain,(
% 2.27/0.70    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f4])).
% 2.27/0.70  fof(f4,axiom,(
% 2.27/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.27/0.70  fof(f1359,plain,(
% 2.27/0.70    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))),
% 2.27/0.70    inference(forward_demodulation,[],[f1345,f250])).
% 2.27/0.70  fof(f250,plain,(
% 2.27/0.70    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f26,f24,f27])).
% 2.27/0.70  fof(f27,plain,(
% 2.27/0.70    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f13])).
% 2.27/0.70  fof(f13,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.27/0.70    inference(ennf_transformation,[],[f6])).
% 2.27/0.70  fof(f6,axiom,(
% 2.27/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 2.27/0.70  fof(f24,plain,(
% 2.27/0.70    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.27/0.70    inference(cnf_transformation,[],[f12])).
% 2.27/0.70  fof(f12,plain,(
% 2.27/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.27/0.70    inference(flattening,[],[f11])).
% 2.27/0.70  fof(f11,plain,(
% 2.27/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.27/0.70    inference(ennf_transformation,[],[f10])).
% 2.27/0.70  fof(f10,negated_conjecture,(
% 2.27/0.70    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 2.27/0.70    inference(negated_conjecture,[],[f9])).
% 2.27/0.70  fof(f9,conjecture,(
% 2.27/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).
% 2.27/0.70  fof(f26,plain,(
% 2.27/0.70    l1_pre_topc(sK0)),
% 2.27/0.70    inference(cnf_transformation,[],[f12])).
% 2.27/0.70  fof(f1345,plain,(
% 2.27/0.70    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f26,f419,f167,f24,f21,f408])).
% 2.27/0.70  fof(f408,plain,(
% 2.27/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~sP5(X3,X2,X0,X1) | r2_hidden(X3,k1_tops_2(X1,X0,X2))) )),
% 2.27/0.70    inference(duplicate_literal_removal,[],[f401])).
% 2.27/0.70  fof(f401,plain,(
% 2.27/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) | ~sP5(X3,X2,X0,X1) | r2_hidden(X3,k1_tops_2(X1,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 2.27/0.70    inference(resolution,[],[f53,f43])).
% 2.27/0.70  fof(f43,plain,(
% 2.27/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f18])).
% 2.27/0.70  fof(f18,plain,(
% 2.27/0.70    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.27/0.70    inference(flattening,[],[f17])).
% 2.27/0.70  fof(f17,plain,(
% 2.27/0.70    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f8])).
% 2.27/0.70  fof(f8,axiom,(
% 2.27/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 2.27/0.70  fof(f53,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X1] : (~m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~sP5(X4,X2,X1,X0) | r2_hidden(X4,k1_tops_2(X0,X1,X2))) )),
% 2.27/0.70    inference(equality_resolution,[],[f34])).
% 2.27/0.70  fof(f34,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_tops_2(X0,X1,X2) != X3) )),
% 2.27/0.70    inference(cnf_transformation,[],[f14])).
% 2.27/0.70  fof(f14,plain,(
% 2.27/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.27/0.70    inference(ennf_transformation,[],[f7])).
% 2.27/0.70  fof(f7,axiom,(
% 2.27/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).
% 2.27/0.70  fof(f21,plain,(
% 2.27/0.70    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.27/0.70    inference(cnf_transformation,[],[f12])).
% 2.27/0.70  fof(f167,plain,(
% 2.27/0.70    ~r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 2.27/0.70    inference(backward_demodulation,[],[f23,f156])).
% 2.27/0.70  fof(f156,plain,(
% 2.27/0.70    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)) )),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f24,f42])).
% 2.27/0.70  fof(f42,plain,(
% 2.27/0.70    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.27/0.70    inference(cnf_transformation,[],[f16])).
% 2.27/0.70  fof(f16,plain,(
% 2.27/0.70    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.27/0.70    inference(ennf_transformation,[],[f3])).
% 2.27/0.70  fof(f3,axiom,(
% 2.27/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.27/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.27/0.70  fof(f23,plain,(
% 2.27/0.70    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 2.27/0.70    inference(cnf_transformation,[],[f12])).
% 2.27/0.70  fof(f419,plain,(
% 2.27/0.70    sP5(k3_xboole_0(sK1,sK2),sK3,sK2,sK0)),
% 2.27/0.70    inference(superposition,[],[f275,f156])).
% 2.27/0.70  fof(f275,plain,(
% 2.27/0.70    ( ! [X0] : (sP5(k9_subset_1(u1_struct_0(sK0),sK1,X0),sK3,X0,sK0)) )),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f22,f25,f54])).
% 2.27/0.70  fof(f54,plain,(
% 2.27/0.70    ( ! [X2,X0,X5,X1] : (sP5(k9_subset_1(u1_struct_0(X0),X5,X1),X2,X1,X0) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.27/0.70    inference(equality_resolution,[],[f28])).
% 2.27/0.70  fof(f28,plain,(
% 2.27/0.70    ( ! [X4,X2,X0,X5,X1] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X5,X2) | k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | sP5(X4,X2,X1,X0)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f14])).
% 2.27/0.70  fof(f25,plain,(
% 2.27/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.27/0.70    inference(cnf_transformation,[],[f12])).
% 2.27/0.70  fof(f22,plain,(
% 2.27/0.70    r2_hidden(sK1,sK3)),
% 2.27/0.70    inference(cnf_transformation,[],[f12])).
% 2.27/0.70  fof(f1371,plain,(
% 2.27/0.70    ~r2_hidden(sK7(k3_xboole_0(sK1,sK2),sK2),sK2)),
% 2.27/0.70    inference(unit_resulting_resolution,[],[f1361,f39])).
% 2.27/0.70  fof(f39,plain,(
% 2.27/0.70    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.27/0.70    inference(cnf_transformation,[],[f15])).
% 2.27/0.70  % SZS output end Proof for theBenchmark
% 2.27/0.70  % (11597)------------------------------
% 2.27/0.70  % (11597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.70  % (11597)Termination reason: Refutation
% 2.27/0.70  
% 2.27/0.70  % (11597)Memory used [KB]: 7803
% 2.27/0.70  % (11597)Time elapsed: 0.294 s
% 2.27/0.70  % (11597)------------------------------
% 2.27/0.70  % (11597)------------------------------
% 2.27/0.70  % (11572)Success in time 0.341 s
%------------------------------------------------------------------------------
