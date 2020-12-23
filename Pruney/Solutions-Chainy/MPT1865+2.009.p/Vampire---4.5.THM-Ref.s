%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 185 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   28
%              Number of atoms          :  202 ( 863 expanded)
%              Number of equality atoms :   26 ( 120 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(resolution,[],[f97,f21])).

fof(f21,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

fof(f97,plain,(
    ! [X2] : ~ r2_hidden(X2,sK1) ),
    inference(resolution,[],[f92,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f91,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f91,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f90,plain,(
    ~ r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f21])).

fof(f89,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f88,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f87,plain,
    ( ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f56,f22])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f55,f23])).

fof(f23,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,X0)
      | m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

% (10375)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f86,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f85,f23])).

fof(f85,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f84,f24])).

fof(f84,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f83,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f82,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f41,f78])).

fof(f78,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(resolution,[],[f75,f21])).

fof(f75,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ) ),
    inference(resolution,[],[f70,f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f69,f39])).

fof(f69,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(resolution,[],[f67,f45])).

fof(f67,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(resolution,[],[f66,f21])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k2_enumset1(X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(X0,X0,X0,X0)))
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f65,f42])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_enumset1(X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(X0,X0,X0,X0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f62,f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,X0)
      | k9_subset_1(u1_struct_0(sK0),X0,sK4(sK0,X0,X1)) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f19,f40])).

fof(f19,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (10373)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (10373)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (10390)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (10369)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (10381)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(resolution,[],[f97,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    r2_hidden(sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,sK1)) )),
% 0.21/0.50    inference(resolution,[],[f92,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f91,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f90,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f36,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ~r2_hidden(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f21])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f88,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f37,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f25,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~r2_hidden(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f87,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f35,f40])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f22])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f55,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v2_tex_2(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f27,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  % (10375)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f23])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f24])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f22])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f82,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v4_pre_topc(sK4(X0,X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k2_enumset1(sK2,sK2,sK2,sK2) != k2_enumset1(sK2,sK2,sK2,sK2) | ~v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(superposition,[],[f41,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.51    inference(resolution,[],[f75,f21])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,sK1) | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) )),
% 0.21/0.51    inference(resolution,[],[f70,f22])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f69,f39])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.51    inference(resolution,[],[f67,f45])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~r2_hidden(sK2,u1_struct_0(sK0)) | k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.51    inference(resolution,[],[f66,f21])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | k2_enumset1(X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(X0,X0,X0,X0))) | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(resolution,[],[f65,f42])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_enumset1(X0,X0,X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(X0,X0,X0,X0))) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f64,f44])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f63,f22])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f62,f23])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | k9_subset_1(u1_struct_0(sK0),X0,sK4(sK0,X0,X1)) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f29,f24])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f40])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (10373)------------------------------
% 0.21/0.51  % (10373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10373)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (10373)Memory used [KB]: 6268
% 0.21/0.51  % (10373)Time elapsed: 0.089 s
% 0.21/0.51  % (10373)------------------------------
% 0.21/0.51  % (10373)------------------------------
% 0.21/0.51  % (10363)Success in time 0.152 s
%------------------------------------------------------------------------------
