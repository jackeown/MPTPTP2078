%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:19 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 472 expanded)
%              Number of leaves         :   17 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  275 (2263 expanded)
%              Number of equality atoms :   48 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1032,plain,(
    $false ),
    inference(resolution,[],[f965,f42])).

fof(f42,plain,(
    ~ r1_tarski(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
                & r1_tarski(X1,X2)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k1_tops_1(sK0,X2))
              & r1_tarski(X1,X2)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (28637)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,k1_tops_1(sK0,X2))
            & r1_tarski(X1,X2)
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,k1_tops_1(sK0,X2))
          & r1_tarski(sK1,X2)
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,k1_tops_1(sK0,X2))
        & r1_tarski(sK1,X2)
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_pre_topc(X1,X0) )
                 => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f965,plain,(
    r1_tarski(sK1,k1_tops_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f519,f946])).

fof(f946,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f945,f80])).

fof(f80,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f74,f68])).

fof(f68,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f74,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f55,f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f945,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f211,f943])).

fof(f943,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f942,f38])).

fof(f942,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f539,f158])).

fof(f158,plain,(
    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f153,f68])).

fof(f153,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f148,f38])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(k3_subset_1(X1,X0),X1) ) ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | r1_tarski(k3_subset_1(X2,X3),X2) ) ),
    inference(forward_demodulation,[],[f120,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f71,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f66,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f55,f45])).

fof(f120,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_subset_1(X2,X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | r1_tarski(k3_subset_1(X2,X3),X2) ) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f539,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f407,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f407,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f101,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f101,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f100,f68])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f99,f40])).

fof(f40,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f51,f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f211,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f206,f68])).

fof(f206,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f137,f38])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f519,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f513,f392])).

fof(f392,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK2),k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f364,f390])).

fof(f390,plain,(
    k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f377,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f377,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f355,f41])).

fof(f41,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f355,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f218,f38])).

fof(f218,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X7,X6)
      | k3_subset_1(k1_tops_1(sK0,X6),k1_tops_1(sK0,X7)) = k4_xboole_0(k1_tops_1(sK0,X6),k1_tops_1(sK0,X7)) ) ),
    inference(resolution,[],[f150,f70])).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_subset_1(X2,X3) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f54,f58])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f53,f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f364,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK2),k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f360,f39])).

fof(f360,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK2),k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f350,f41])).

fof(f350,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,X0),k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f217,f38])).

fof(f217,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X5,X4)
      | k1_tops_1(sK0,X5) = k3_subset_1(k1_tops_1(sK0,X4),k3_subset_1(k1_tops_1(sK0,X4),k1_tops_1(sK0,X5))) ) ),
    inference(resolution,[],[f150,f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = X3 ) ),
    inference(resolution,[],[f55,f58])).

fof(f513,plain,(
    r1_tarski(k3_subset_1(k1_tops_1(sK0,sK2),k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f509,f155])).

fof(f155,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | r1_tarski(k3_subset_1(X2,X3),X2) ) ),
    inference(resolution,[],[f148,f58])).

fof(f509,plain,(
    r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f506,f39])).

fof(f506,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f503,f390])).

fof(f503,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f498,f41])).

fof(f498,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f215,f38])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,X0)
      | r1_tarski(k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f150,f155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28632)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (28640)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (28632)Refutation not found, incomplete strategy% (28632)------------------------------
% 0.21/0.52  % (28632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28640)Refutation not found, incomplete strategy% (28640)------------------------------
% 0.21/0.52  % (28640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28632)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28632)Memory used [KB]: 10618
% 0.21/0.52  % (28632)Time elapsed: 0.071 s
% 0.21/0.52  % (28632)------------------------------
% 0.21/0.52  % (28632)------------------------------
% 0.21/0.52  % (28640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28640)Memory used [KB]: 1663
% 0.21/0.52  % (28640)Time elapsed: 0.078 s
% 0.21/0.52  % (28640)------------------------------
% 0.21/0.52  % (28640)------------------------------
% 1.40/0.55  % (28633)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.40/0.56  % (28628)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.40/0.56  % (28625)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.40/0.57  % (28636)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.40/0.57  % (28641)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.40/0.57  % (28626)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.40/0.57  % (28639)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.40/0.57  % (28627)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.40/0.58  % (28627)Refutation not found, incomplete strategy% (28627)------------------------------
% 1.40/0.58  % (28627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (28627)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (28627)Memory used [KB]: 10618
% 1.40/0.58  % (28627)Time elapsed: 0.127 s
% 1.40/0.58  % (28627)------------------------------
% 1.40/0.58  % (28627)------------------------------
% 1.40/0.58  % (28644)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.40/0.58  % (28629)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.40/0.58  % (28644)Refutation not found, incomplete strategy% (28644)------------------------------
% 1.40/0.58  % (28644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (28644)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (28644)Memory used [KB]: 6140
% 1.40/0.58  % (28644)Time elapsed: 0.137 s
% 1.40/0.58  % (28644)------------------------------
% 1.40/0.58  % (28644)------------------------------
% 1.40/0.58  % (28634)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.40/0.58  % (28647)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.40/0.58  % (28634)Refutation not found, incomplete strategy% (28634)------------------------------
% 1.40/0.58  % (28634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (28634)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (28634)Memory used [KB]: 10490
% 1.40/0.58  % (28634)Time elapsed: 0.144 s
% 1.40/0.58  % (28634)------------------------------
% 1.40/0.58  % (28634)------------------------------
% 1.40/0.58  % (28635)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.40/0.58  % (28647)Refutation not found, incomplete strategy% (28647)------------------------------
% 1.40/0.58  % (28647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (28647)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (28647)Memory used [KB]: 10618
% 1.40/0.58  % (28647)Time elapsed: 0.142 s
% 1.40/0.58  % (28647)------------------------------
% 1.40/0.58  % (28647)------------------------------
% 1.40/0.58  % (28642)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.40/0.58  % (28631)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.59  % (28633)Refutation found. Thanks to Tanya!
% 1.40/0.59  % SZS status Theorem for theBenchmark
% 1.40/0.59  % SZS output start Proof for theBenchmark
% 1.40/0.59  fof(f1032,plain,(
% 1.40/0.59    $false),
% 1.40/0.59    inference(resolution,[],[f965,f42])).
% 1.40/0.59  fof(f42,plain,(
% 1.40/0.59    ~r1_tarski(sK1,k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(cnf_transformation,[],[f34])).
% 1.40/0.59  fof(f34,plain,(
% 1.40/0.59    ((~r1_tarski(sK1,k1_tops_1(sK0,sK2)) & r1_tarski(sK1,sK2) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.40/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33,f32,f31])).
% 1.40/0.59  fof(f31,plain,(
% 1.40/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X1,k1_tops_1(sK0,X2)) & r1_tarski(X1,X2) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.40/0.59    introduced(choice_axiom,[])).
% 1.40/0.59  % (28637)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.40/0.59  fof(f32,plain,(
% 1.40/0.59    ? [X1] : (? [X2] : (~r1_tarski(X1,k1_tops_1(sK0,X2)) & r1_tarski(X1,X2) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(sK1,k1_tops_1(sK0,X2)) & r1_tarski(sK1,X2) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.59    introduced(choice_axiom,[])).
% 1.40/0.59  fof(f33,plain,(
% 1.40/0.59    ? [X2] : (~r1_tarski(sK1,k1_tops_1(sK0,X2)) & r1_tarski(sK1,X2) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(sK1,k1_tops_1(sK0,sK2)) & r1_tarski(sK1,sK2) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.40/0.59    introduced(choice_axiom,[])).
% 1.40/0.59  fof(f18,plain,(
% 1.40/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.40/0.59    inference(flattening,[],[f17])).
% 1.40/0.59  fof(f17,plain,(
% 1.40/0.59    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k1_tops_1(X0,X2)) & (r1_tarski(X1,X2) & v3_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f16])).
% 1.40/0.59  fof(f16,negated_conjecture,(
% 1.40/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.40/0.59    inference(negated_conjecture,[],[f15])).
% 1.40/0.59  fof(f15,conjecture,(
% 1.40/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.40/0.59  fof(f965,plain,(
% 1.40/0.59    r1_tarski(sK1,k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(backward_demodulation,[],[f519,f946])).
% 1.40/0.59  fof(f946,plain,(
% 1.40/0.59    sK1 = k1_tops_1(sK0,sK1)),
% 1.40/0.59    inference(forward_demodulation,[],[f945,f80])).
% 1.40/0.59  fof(f80,plain,(
% 1.40/0.59    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.40/0.59    inference(forward_demodulation,[],[f74,f68])).
% 1.40/0.59  fof(f68,plain,(
% 1.40/0.59    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.40/0.59    inference(resolution,[],[f54,f38])).
% 1.40/0.59  fof(f38,plain,(
% 1.40/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.59    inference(cnf_transformation,[],[f34])).
% 1.40/0.59  fof(f54,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f25])).
% 1.40/0.59  fof(f25,plain,(
% 1.40/0.59    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.59    inference(ennf_transformation,[],[f4])).
% 1.40/0.59  fof(f4,axiom,(
% 1.40/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.40/0.59  fof(f74,plain,(
% 1.40/0.59    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.40/0.59    inference(resolution,[],[f55,f38])).
% 1.40/0.59  fof(f55,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.40/0.59    inference(cnf_transformation,[],[f26])).
% 1.40/0.59  fof(f26,plain,(
% 1.40/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.59    inference(ennf_transformation,[],[f6])).
% 1.40/0.59  fof(f6,axiom,(
% 1.40/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.40/0.59  fof(f945,plain,(
% 1.40/0.59    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)),
% 1.40/0.59    inference(backward_demodulation,[],[f211,f943])).
% 1.40/0.59  fof(f943,plain,(
% 1.40/0.59    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.40/0.59    inference(resolution,[],[f942,f38])).
% 1.40/0.59  fof(f942,plain,(
% 1.40/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.40/0.59    inference(resolution,[],[f539,f158])).
% 1.40/0.59  fof(f158,plain,(
% 1.40/0.59    r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.40/0.59    inference(forward_demodulation,[],[f153,f68])).
% 1.40/0.59  fof(f153,plain,(
% 1.40/0.59    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.40/0.59    inference(resolution,[],[f148,f38])).
% 1.40/0.59  fof(f148,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1)) )),
% 1.40/0.59    inference(resolution,[],[f125,f43])).
% 1.40/0.59  fof(f43,plain,(
% 1.40/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f1])).
% 1.40/0.59  fof(f1,axiom,(
% 1.40/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.59  fof(f125,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | r1_tarski(k3_subset_1(X2,X3),X2)) )),
% 1.40/0.59    inference(forward_demodulation,[],[f120,f77])).
% 1.40/0.59  fof(f77,plain,(
% 1.40/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.40/0.59    inference(forward_demodulation,[],[f72,f71])).
% 1.40/0.59  fof(f71,plain,(
% 1.40/0.59    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.40/0.59    inference(forward_demodulation,[],[f66,f46])).
% 1.40/0.59  fof(f46,plain,(
% 1.40/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.59    inference(cnf_transformation,[],[f2])).
% 1.40/0.59  fof(f2,axiom,(
% 1.40/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.40/0.59  fof(f66,plain,(
% 1.40/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.40/0.59    inference(resolution,[],[f54,f45])).
% 1.40/0.59  fof(f45,plain,(
% 1.40/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f8])).
% 1.40/0.59  fof(f8,axiom,(
% 1.40/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.40/0.59  fof(f72,plain,(
% 1.40/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.40/0.59    inference(resolution,[],[f55,f45])).
% 1.40/0.59  fof(f120,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r1_tarski(k3_subset_1(X2,X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | r1_tarski(k3_subset_1(X2,X3),X2)) )),
% 1.40/0.59    inference(resolution,[],[f56,f60])).
% 1.40/0.59  fof(f60,plain,(
% 1.40/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.40/0.59    inference(forward_demodulation,[],[f47,f44])).
% 1.40/0.59  fof(f44,plain,(
% 1.40/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.40/0.59    inference(cnf_transformation,[],[f3])).
% 1.40/0.59  fof(f3,axiom,(
% 1.40/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.40/0.59  fof(f47,plain,(
% 1.40/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f5])).
% 1.40/0.59  fof(f5,axiom,(
% 1.40/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.40/0.59  fof(f56,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X2),X1)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f28])).
% 1.40/0.59  fof(f28,plain,(
% 1.40/0.59    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.59    inference(flattening,[],[f27])).
% 1.40/0.59  fof(f27,plain,(
% 1.40/0.59    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.59    inference(ennf_transformation,[],[f7])).
% 1.40/0.59  fof(f7,axiom,(
% 1.40/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 1.40/0.59  fof(f539,plain,(
% 1.40/0.59    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.40/0.59    inference(resolution,[],[f407,f58])).
% 1.40/0.59  fof(f58,plain,(
% 1.40/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f36])).
% 1.40/0.59  fof(f36,plain,(
% 1.40/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.40/0.59    inference(nnf_transformation,[],[f9])).
% 1.40/0.59  fof(f9,axiom,(
% 1.40/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.40/0.59  fof(f407,plain,(
% 1.40/0.59    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.59    inference(resolution,[],[f102,f37])).
% 1.40/0.59  fof(f37,plain,(
% 1.40/0.59    l1_pre_topc(sK0)),
% 1.40/0.59    inference(cnf_transformation,[],[f34])).
% 1.40/0.59  fof(f102,plain,(
% 1.40/0.59    ~l1_pre_topc(sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.59    inference(resolution,[],[f101,f49])).
% 1.40/0.59  fof(f49,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f21])).
% 1.40/0.59  fof(f21,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(flattening,[],[f20])).
% 1.40/0.59  fof(f20,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f11])).
% 1.40/0.59  fof(f11,axiom,(
% 1.40/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.40/0.59  fof(f101,plain,(
% 1.40/0.59    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.59    inference(forward_demodulation,[],[f100,f68])).
% 1.40/0.59  fof(f100,plain,(
% 1.40/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.40/0.59    inference(resolution,[],[f99,f40])).
% 1.40/0.59  fof(f40,plain,(
% 1.40/0.59    v3_pre_topc(sK1,sK0)),
% 1.40/0.59    inference(cnf_transformation,[],[f34])).
% 1.40/0.59  fof(f99,plain,(
% 1.40/0.59    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 1.40/0.59    inference(resolution,[],[f51,f37])).
% 1.40/0.59  fof(f51,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f35])).
% 1.40/0.59  fof(f35,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(nnf_transformation,[],[f22])).
% 1.40/0.59  fof(f22,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f13])).
% 1.40/0.59  fof(f13,axiom,(
% 1.40/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 1.40/0.59  fof(f211,plain,(
% 1.40/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 1.40/0.59    inference(forward_demodulation,[],[f206,f68])).
% 1.40/0.59  fof(f206,plain,(
% 1.40/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.40/0.59    inference(resolution,[],[f137,f38])).
% 1.40/0.59  fof(f137,plain,(
% 1.40/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.40/0.59    inference(resolution,[],[f48,f37])).
% 1.40/0.59  fof(f48,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f19])).
% 1.40/0.59  fof(f19,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f12])).
% 1.40/0.59  fof(f12,axiom,(
% 1.40/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.40/0.59  fof(f519,plain,(
% 1.40/0.59    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(forward_demodulation,[],[f513,f392])).
% 1.40/0.59  fof(f392,plain,(
% 1.40/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK2),k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)))),
% 1.40/0.59    inference(backward_demodulation,[],[f364,f390])).
% 1.40/0.59  fof(f390,plain,(
% 1.40/0.59    k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))),
% 1.40/0.59    inference(resolution,[],[f377,f39])).
% 1.40/0.59  fof(f39,plain,(
% 1.40/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.59    inference(cnf_transformation,[],[f34])).
% 1.40/0.59  fof(f377,plain,(
% 1.40/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))),
% 1.40/0.59    inference(resolution,[],[f355,f41])).
% 1.40/0.59  fof(f41,plain,(
% 1.40/0.59    r1_tarski(sK1,sK2)),
% 1.40/0.59    inference(cnf_transformation,[],[f34])).
% 1.40/0.59  fof(f355,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))) )),
% 1.40/0.59    inference(resolution,[],[f218,f38])).
% 1.40/0.59  fof(f218,plain,(
% 1.40/0.59    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X7,X6) | k3_subset_1(k1_tops_1(sK0,X6),k1_tops_1(sK0,X7)) = k4_xboole_0(k1_tops_1(sK0,X6),k1_tops_1(sK0,X7))) )),
% 1.40/0.59    inference(resolution,[],[f150,f70])).
% 1.40/0.59  fof(f70,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_subset_1(X2,X3) = k4_xboole_0(X2,X3)) )),
% 1.40/0.59    inference(resolution,[],[f54,f58])).
% 1.40/0.59  fof(f150,plain,(
% 1.40/0.59    ( ! [X0,X1] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1)) )),
% 1.40/0.59    inference(resolution,[],[f53,f37])).
% 1.40/0.59  fof(f53,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f24])).
% 1.40/0.59  fof(f24,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(flattening,[],[f23])).
% 1.40/0.59  fof(f23,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f14])).
% 1.40/0.59  fof(f14,axiom,(
% 1.40/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.40/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.40/0.59  fof(f364,plain,(
% 1.40/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK2),k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)))),
% 1.40/0.59    inference(resolution,[],[f360,f39])).
% 1.40/0.59  fof(f360,plain,(
% 1.40/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK2),k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)))),
% 1.40/0.59    inference(resolution,[],[f350,f41])).
% 1.40/0.59  fof(f350,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,X0),k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)))) )),
% 1.40/0.59    inference(resolution,[],[f217,f38])).
% 1.40/0.59  fof(f217,plain,(
% 1.40/0.59    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X5,X4) | k1_tops_1(sK0,X5) = k3_subset_1(k1_tops_1(sK0,X4),k3_subset_1(k1_tops_1(sK0,X4),k1_tops_1(sK0,X5)))) )),
% 1.40/0.59    inference(resolution,[],[f150,f76])).
% 1.40/0.59  fof(f76,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_subset_1(X2,k3_subset_1(X2,X3)) = X3) )),
% 1.40/0.59    inference(resolution,[],[f55,f58])).
% 1.40/0.59  fof(f513,plain,(
% 1.40/0.59    r1_tarski(k3_subset_1(k1_tops_1(sK0,sK2),k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(resolution,[],[f509,f155])).
% 1.40/0.59  fof(f155,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r1_tarski(X3,X2) | r1_tarski(k3_subset_1(X2,X3),X2)) )),
% 1.40/0.59    inference(resolution,[],[f148,f58])).
% 1.40/0.59  fof(f509,plain,(
% 1.40/0.59    r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(resolution,[],[f506,f39])).
% 1.40/0.59  fof(f506,plain,(
% 1.40/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(forward_demodulation,[],[f503,f390])).
% 1.40/0.59  fof(f503,plain,(
% 1.40/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_subset_1(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK2))),
% 1.40/0.59    inference(resolution,[],[f498,f41])).
% 1.40/0.59  fof(f498,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,X0))) )),
% 1.40/0.59    inference(resolution,[],[f215,f38])).
% 1.40/0.59  fof(f215,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | r1_tarski(k3_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)),k1_tops_1(sK0,X0))) )),
% 1.40/0.59    inference(resolution,[],[f150,f155])).
% 1.40/0.59  % SZS output end Proof for theBenchmark
% 1.40/0.59  % (28633)------------------------------
% 1.40/0.59  % (28633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (28633)Termination reason: Refutation
% 1.40/0.59  
% 1.40/0.59  % (28633)Memory used [KB]: 2174
% 1.40/0.59  % (28633)Time elapsed: 0.143 s
% 1.40/0.59  % (28633)------------------------------
% 1.40/0.59  % (28633)------------------------------
% 1.40/0.59  % (28631)Refutation not found, incomplete strategy% (28631)------------------------------
% 1.40/0.59  % (28631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (28631)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.59  
% 1.40/0.59  % (28631)Memory used [KB]: 6268
% 1.40/0.59  % (28631)Time elapsed: 0.143 s
% 1.40/0.59  % (28631)------------------------------
% 1.40/0.59  % (28631)------------------------------
% 1.40/0.59  % (28623)Success in time 0.22 s
%------------------------------------------------------------------------------
