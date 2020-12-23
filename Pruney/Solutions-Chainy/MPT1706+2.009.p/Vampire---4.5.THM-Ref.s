%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:45 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 149 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   19
%              Number of atoms          :  242 (1074 expanded)
%              Number of equality atoms :   17 ( 117 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112,f58])).

% (2150)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f28,plain,
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

fof(f29,plain,
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f112,plain,(
    ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f111,plain,(
    ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f109,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f109,plain,(
    v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f56,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f104,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f104,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f97,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f67,f85])).

fof(f85,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f73,f39])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f57,f38])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK1),X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | r1_tarski(k2_tarski(sK3,sK3),X0) ) ),
    inference(resolution,[],[f65,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f65,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.51  % (2147)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (2157)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (2160)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (2145)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2143)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2145)Refutation not found, incomplete strategy% (2145)------------------------------
% 0.20/0.52  % (2145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2145)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2145)Memory used [KB]: 10746
% 0.20/0.52  % (2145)Time elapsed: 0.108 s
% 0.20/0.52  % (2145)------------------------------
% 0.20/0.52  % (2145)------------------------------
% 0.20/0.52  % (2148)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (2168)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.52  % (2148)Refutation found. Thanks to Tanya!
% 1.29/0.52  % SZS status Theorem for theBenchmark
% 1.29/0.52  % SZS output start Proof for theBenchmark
% 1.29/0.52  fof(f113,plain,(
% 1.29/0.52    $false),
% 1.29/0.52    inference(subsumption_resolution,[],[f112,f58])).
% 1.29/0.52  % (2150)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.52  fof(f58,plain,(
% 1.29/0.52    l1_pre_topc(sK1)),
% 1.29/0.52    inference(resolution,[],[f57,f36])).
% 1.29/0.52  fof(f36,plain,(
% 1.29/0.52    m1_pre_topc(sK1,sK0)),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f30,plain,(
% 1.29/0.52    (((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.29/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28,f27,f26])).
% 1.29/0.52  fof(f26,plain,(
% 1.29/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f27,plain,(
% 1.29/0.52    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f28,plain,(
% 1.29/0.52    ? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f29,plain,(
% 1.29/0.52    ? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK1))) => (! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f15,plain,(
% 1.29/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.29/0.52    inference(flattening,[],[f14])).
% 1.29/0.52  fof(f14,plain,(
% 1.29/0.52    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f13])).
% 1.29/0.52  fof(f13,plain,(
% 1.29/0.52    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 1.29/0.52    inference(pure_predicate_removal,[],[f12])).
% 1.29/0.52  fof(f12,negated_conjecture,(
% 1.29/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 1.29/0.52    inference(negated_conjecture,[],[f11])).
% 1.29/0.52  fof(f11,conjecture,(
% 1.29/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).
% 1.29/0.52  fof(f57,plain,(
% 1.29/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.29/0.52    inference(resolution,[],[f49,f34])).
% 1.29/0.52  fof(f34,plain,(
% 1.29/0.52    l1_pre_topc(sK0)),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f49,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f22])).
% 1.29/0.52  fof(f22,plain,(
% 1.29/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.29/0.52    inference(ennf_transformation,[],[f8])).
% 1.29/0.52  fof(f8,axiom,(
% 1.29/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.29/0.52  fof(f112,plain,(
% 1.29/0.52    ~l1_pre_topc(sK1)),
% 1.29/0.52    inference(resolution,[],[f111,f50])).
% 1.29/0.52  fof(f50,plain,(
% 1.29/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f23,plain,(
% 1.29/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.29/0.52    inference(ennf_transformation,[],[f7])).
% 1.29/0.52  fof(f7,axiom,(
% 1.29/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.29/0.52  fof(f111,plain,(
% 1.29/0.52    ~l1_struct_0(sK1)),
% 1.29/0.52    inference(subsumption_resolution,[],[f110,f35])).
% 1.29/0.52  fof(f35,plain,(
% 1.29/0.52    ~v2_struct_0(sK1)),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f110,plain,(
% 1.29/0.52    ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.29/0.52    inference(resolution,[],[f109,f48])).
% 1.29/0.52  fof(f48,plain,(
% 1.29/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f21])).
% 1.29/0.52  fof(f21,plain,(
% 1.29/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.29/0.52    inference(flattening,[],[f20])).
% 1.29/0.52  fof(f20,plain,(
% 1.29/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f9])).
% 1.29/0.52  fof(f9,axiom,(
% 1.29/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.29/0.52  fof(f109,plain,(
% 1.29/0.52    v1_xboole_0(u1_struct_0(sK1))),
% 1.29/0.52    inference(subsumption_resolution,[],[f108,f56])).
% 1.29/0.52  fof(f56,plain,(
% 1.29/0.52    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.52    inference(equality_resolution,[],[f41])).
% 1.29/0.52  fof(f41,plain,(
% 1.29/0.52    ( ! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f108,plain,(
% 1.29/0.52    v1_xboole_0(u1_struct_0(sK1)) | m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.52    inference(resolution,[],[f104,f46])).
% 1.29/0.52  fof(f46,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f18])).
% 1.29/0.52  fof(f18,plain,(
% 1.29/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.29/0.52    inference(ennf_transformation,[],[f4])).
% 1.29/0.52  fof(f4,axiom,(
% 1.29/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.29/0.52  fof(f104,plain,(
% 1.29/0.52    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.29/0.52    inference(resolution,[],[f97,f55])).
% 1.29/0.52  fof(f55,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.29/0.52    inference(definition_unfolding,[],[f51,f42])).
% 1.29/0.52  fof(f42,plain,(
% 1.29/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f2])).
% 1.29/0.52  fof(f2,axiom,(
% 1.29/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.52  fof(f51,plain,(
% 1.29/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f32])).
% 1.29/0.52  fof(f32,plain,(
% 1.29/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.29/0.52    inference(nnf_transformation,[],[f3])).
% 1.29/0.52  fof(f3,axiom,(
% 1.29/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.29/0.52  fof(f97,plain,(
% 1.29/0.52    r1_tarski(k2_tarski(sK3,sK3),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.29/0.52    inference(resolution,[],[f67,f85])).
% 1.29/0.52  fof(f85,plain,(
% 1.29/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.29/0.52    inference(resolution,[],[f84,f43])).
% 1.29/0.52  fof(f43,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f31])).
% 1.29/0.52  fof(f31,plain,(
% 1.29/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.29/0.52    inference(nnf_transformation,[],[f6])).
% 1.29/0.52  fof(f6,axiom,(
% 1.29/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.52  fof(f84,plain,(
% 1.29/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.29/0.52    inference(resolution,[],[f73,f39])).
% 1.29/0.52  fof(f39,plain,(
% 1.29/0.52    m1_pre_topc(sK1,sK2)),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f73,plain,(
% 1.29/0.52    ( ! [X2] : (~m1_pre_topc(X2,sK2) | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.52    inference(resolution,[],[f47,f59])).
% 1.29/0.52  fof(f59,plain,(
% 1.29/0.52    l1_pre_topc(sK2)),
% 1.29/0.52    inference(resolution,[],[f57,f38])).
% 1.29/0.52  fof(f38,plain,(
% 1.29/0.52    m1_pre_topc(sK2,sK0)),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f47,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f19])).
% 1.29/0.52  fof(f19,plain,(
% 1.29/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.29/0.52    inference(ennf_transformation,[],[f10])).
% 1.29/0.52  fof(f10,axiom,(
% 1.29/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.29/0.52  fof(f67,plain,(
% 1.29/0.52    ( ! [X0] : (~r1_tarski(u1_struct_0(sK1),X0) | v1_xboole_0(u1_struct_0(sK1)) | r1_tarski(k2_tarski(sK3,sK3),X0)) )),
% 1.29/0.52    inference(resolution,[],[f65,f53])).
% 1.29/0.52  fof(f53,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f25])).
% 1.29/0.52  fof(f25,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.29/0.52    inference(flattening,[],[f24])).
% 1.29/0.52  fof(f24,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.29/0.52    inference(ennf_transformation,[],[f1])).
% 1.29/0.52  fof(f1,axiom,(
% 1.29/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.29/0.52  fof(f65,plain,(
% 1.29/0.52    r1_tarski(k2_tarski(sK3,sK3),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.29/0.52    inference(resolution,[],[f54,f63])).
% 1.29/0.52  fof(f63,plain,(
% 1.29/0.52    r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.29/0.52    inference(resolution,[],[f45,f40])).
% 1.29/0.52  fof(f40,plain,(
% 1.29/0.52    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f45,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f17])).
% 1.29/0.52  fof(f17,plain,(
% 1.29/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.29/0.52    inference(flattening,[],[f16])).
% 1.29/0.52  fof(f16,plain,(
% 1.29/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.29/0.52    inference(ennf_transformation,[],[f5])).
% 1.29/0.52  fof(f5,axiom,(
% 1.29/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.29/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.29/0.52  fof(f54,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1)) )),
% 1.29/0.52    inference(definition_unfolding,[],[f52,f42])).
% 1.29/0.52  fof(f52,plain,(
% 1.29/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f32])).
% 1.29/0.52  % SZS output end Proof for theBenchmark
% 1.29/0.52  % (2148)------------------------------
% 1.29/0.52  % (2148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (2148)Termination reason: Refutation
% 1.29/0.52  
% 1.29/0.52  % (2148)Memory used [KB]: 6268
% 1.29/0.52  % (2148)Time elapsed: 0.120 s
% 1.29/0.52  % (2148)------------------------------
% 1.29/0.52  % (2148)------------------------------
% 1.29/0.52  % (2144)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.52  % (2154)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.53  % (2161)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.53  % (2154)Refutation not found, incomplete strategy% (2154)------------------------------
% 1.29/0.53  % (2154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (2154)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (2154)Memory used [KB]: 10618
% 1.29/0.53  % (2154)Time elapsed: 0.119 s
% 1.29/0.53  % (2154)------------------------------
% 1.29/0.53  % (2154)------------------------------
% 1.29/0.53  % (2142)Success in time 0.171 s
%------------------------------------------------------------------------------
