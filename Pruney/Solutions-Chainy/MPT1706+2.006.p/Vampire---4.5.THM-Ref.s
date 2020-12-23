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
% DateTime   : Thu Dec  3 13:17:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 138 expanded)
%              Number of leaves         :   14 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  250 (1074 expanded)
%              Number of equality atoms :   15 ( 113 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(subsumption_resolution,[],[f89,f55])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK3 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f89,plain,(
    ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f88,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f88,plain,(
    ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f86,plain,(
    v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f85,f56])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X2] :
      ( m1_subset_1(sK3,u1_struct_0(X2))
      | ~ m1_pre_topc(sK1,X2)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK3,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f76,f60])).

fof(f60,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f47,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r2_hidden(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (2409)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (2424)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.51  % (2407)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (2407)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(subsumption_resolution,[],[f89,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    l1_pre_topc(sK1)),
% 0.19/0.51    inference(resolution,[],[f54,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    m1_pre_topc(sK1,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    (((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25,f24,f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK1))) => (! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.19/0.51  fof(f10,negated_conjecture,(
% 0.19/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.19/0.51    inference(negated_conjecture,[],[f9])).
% 0.19/0.51  fof(f9,conjecture,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.19/0.51    inference(resolution,[],[f43,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    l1_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1)),
% 0.19/0.51    inference(resolution,[],[f88,f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    ~l1_struct_0(sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f87,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ~v2_struct_0(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.19/0.51    inference(resolution,[],[f86,f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    v1_xboole_0(u1_struct_0(sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f85,f56])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    l1_pre_topc(sK2)),
% 0.19/0.51    inference(resolution,[],[f54,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    m1_pre_topc(sK2,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f83,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    m1_pre_topc(sK1,sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ~m1_pre_topc(sK1,sK2) | v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK2)),
% 0.19/0.51    inference(resolution,[],[f81,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.19/0.51    inference(equality_resolution,[],[f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ( ! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    ( ! [X2] : (m1_subset_1(sK3,u1_struct_0(X2)) | ~m1_pre_topc(sK1,X2) | v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(X2)) )),
% 0.19/0.51    inference(resolution,[],[f78,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK3,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.19/0.51    inference(resolution,[],[f76,f60])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.19/0.51    inference(resolution,[],[f47,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r2_hidden(X2,u1_struct_0(X0))) )),
% 0.19/0.51    inference(resolution,[],[f74,f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(rectify,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(nnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f44,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.51    inference(nnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (2407)------------------------------
% 0.19/0.51  % (2407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2407)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (2407)Memory used [KB]: 6268
% 0.19/0.51  % (2407)Time elapsed: 0.105 s
% 0.19/0.51  % (2407)------------------------------
% 0.19/0.51  % (2407)------------------------------
% 0.19/0.51  % (2409)Refutation not found, incomplete strategy% (2409)------------------------------
% 0.19/0.51  % (2409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2409)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2409)Memory used [KB]: 10746
% 0.19/0.51  % (2409)Time elapsed: 0.103 s
% 0.19/0.51  % (2409)------------------------------
% 0.19/0.51  % (2409)------------------------------
% 0.19/0.51  % (2408)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (2416)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (2402)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (2404)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (2406)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (2417)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (2400)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (2401)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (2400)Refutation not found, incomplete strategy% (2400)------------------------------
% 0.19/0.52  % (2400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2400)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2400)Memory used [KB]: 1663
% 0.19/0.52  % (2400)Time elapsed: 0.102 s
% 0.19/0.52  % (2400)------------------------------
% 0.19/0.52  % (2400)------------------------------
% 0.19/0.52  % (2410)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (2410)Refutation not found, incomplete strategy% (2410)------------------------------
% 0.19/0.52  % (2410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2410)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2410)Memory used [KB]: 10618
% 0.19/0.52  % (2410)Time elapsed: 0.117 s
% 0.19/0.52  % (2421)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (2425)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (2418)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (2399)Success in time 0.172 s
%------------------------------------------------------------------------------
