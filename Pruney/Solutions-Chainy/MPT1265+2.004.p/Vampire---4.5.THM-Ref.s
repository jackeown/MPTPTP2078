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
% DateTime   : Thu Dec  3 13:12:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 278 expanded)
%              Number of leaves         :   13 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          :  195 (1785 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f218,f253,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f253,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f250,f59])).

fof(f59,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f53,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f53,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f250,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f32,f191,f249,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f249,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f248,f94])).

fof(f94,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f32,f36,f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f248,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f247,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f247,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(forward_demodulation,[],[f246,f166])).

fof(f166,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,sK1) ),
    inference(unit_resulting_resolution,[],[f141,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f141,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f33,f59])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f246,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(forward_demodulation,[],[f96,f59])).

fof(f96,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f32,f37,f35,f33,f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f35,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f191,plain,(
    ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f138,f156])).

fof(f156,plain,(
    ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(k2_struct_0(sK0),X0,sK2) ),
    inference(unit_resulting_resolution,[],[f139,f40])).

fof(f139,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f34,f59])).

fof(f138,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f38,f59])).

fof(f38,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f218,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k2_struct_0(sK0)) ),
    inference(superposition,[],[f51,f171])).

fof(f171,plain,(
    k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f140,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f140,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f68,f59])).

fof(f68,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (21068)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.45  % (21068)Refutation not found, incomplete strategy% (21068)------------------------------
% 0.20/0.45  % (21068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (21082)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.46  % (21068)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (21068)Memory used [KB]: 10746
% 0.20/0.46  % (21068)Time elapsed: 0.069 s
% 0.20/0.47  % (21068)------------------------------
% 0.20/0.47  % (21068)------------------------------
% 0.20/0.48  % (21076)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.48  % (21080)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.48  % (21086)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (21073)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (21064)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (21079)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.49  % (21071)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (21073)Refutation not found, incomplete strategy% (21073)------------------------------
% 0.20/0.49  % (21073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21073)Memory used [KB]: 10618
% 0.20/0.49  % (21073)Time elapsed: 0.094 s
% 0.20/0.49  % (21073)------------------------------
% 0.20/0.49  % (21073)------------------------------
% 0.20/0.49  % (21065)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (21065)Refutation not found, incomplete strategy% (21065)------------------------------
% 0.20/0.49  % (21065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21065)Memory used [KB]: 10618
% 0.20/0.49  % (21065)Time elapsed: 0.090 s
% 0.20/0.49  % (21065)------------------------------
% 0.20/0.49  % (21065)------------------------------
% 0.20/0.49  % (21079)Refutation not found, incomplete strategy% (21079)------------------------------
% 0.20/0.49  % (21079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21079)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21079)Memory used [KB]: 1663
% 0.20/0.49  % (21079)Time elapsed: 0.085 s
% 0.20/0.49  % (21079)------------------------------
% 0.20/0.49  % (21079)------------------------------
% 0.20/0.49  % (21080)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f218,f253,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(forward_demodulation,[],[f250,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f53,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f32,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27,f26,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f32,f191,f249,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(forward_demodulation,[],[f248,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f32,f36,f34,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v1_tops_1(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(forward_demodulation,[],[f247,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f246,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,sK1)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f141,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f33,f59])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f96,f59])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f31,f32,f37,f35,f33,f34,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v1_tops_1(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v3_pre_topc(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f138,f156])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    ( ! [X0] : (k3_xboole_0(X0,sK2) = k9_subset_1(k2_struct_0(sK0),X0,sK2)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f139,f40])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f34,f59])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f38,f59])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),k2_struct_0(sK0))) )),
% 0.20/0.49    inference(superposition,[],[f51,f171])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f140,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    r1_tarski(sK1,k2_struct_0(sK0))),
% 0.20/0.49    inference(backward_demodulation,[],[f68,f59])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f33,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (21080)------------------------------
% 0.20/0.49  % (21080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21080)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (21080)Memory used [KB]: 1663
% 0.20/0.49  % (21080)Time elapsed: 0.085 s
% 0.20/0.49  % (21080)------------------------------
% 0.20/0.49  % (21080)------------------------------
% 0.20/0.49  % (21067)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (21058)Success in time 0.139 s
%------------------------------------------------------------------------------
