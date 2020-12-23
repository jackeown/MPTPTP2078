%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t68_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:30 EDT 2019

% Result     : Theorem 109.76s
% Output     : Refutation 109.76s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 424 expanded)
%              Number of leaves         :   13 ( 139 expanded)
%              Depth                    :   18
%              Number of atoms          :  165 (1221 expanded)
%              Number of equality atoms :   26 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238081,plain,(
    $false ),
    inference(subsumption_resolution,[],[f238038,f143])).

fof(f143,plain,(
    ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f80,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',t3_subset)).

fof(f80,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',t68_tops_1)).

fof(f238038,plain,(
    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f1648,f16335])).

fof(f16335,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f571,f204])).

fof(f204,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f188,f78])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f188,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f133,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',d2_tops_1)).

fof(f133,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f117,f78])).

fof(f117,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f79,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',dt_k2_tops_1)).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f571,plain,(
    ! [X4] : k3_xboole_0(X4,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X4) ),
    inference(backward_demodulation,[],[f548,f547])).

fof(f547,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X4) ),
    inference(resolution,[],[f202,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',commutativity_k9_subset_1)).

fof(f202,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f186,f78])).

fof(f186,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f133,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',dt_k2_pre_topc)).

fof(f548,plain,(
    ! [X5] : k3_xboole_0(X5,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),X5,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f202,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',redefinition_k9_subset_1)).

fof(f1648,plain,(
    ! [X3] : m1_subset_1(k3_xboole_0(X3,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1641,f1640])).

fof(f1640,plain,(
    ! [X2] : k3_xboole_0(X2,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(k2_tops_1(sK0,sK1),X2,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f746,f100])).

fof(f746,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f417,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f417,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f416,f132])).

fof(f132,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f116,f78])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f79,f88])).

fof(f416,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(forward_demodulation,[],[f415,f131])).

fof(f131,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f115,f78])).

fof(f115,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f79,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',projectivity_k2_pre_topc)).

fof(f415,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(forward_demodulation,[],[f414,f259])).

fof(f259,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f243,f78])).

fof(f243,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f126,f90])).

fof(f126,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f79,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',dt_k3_subset_1)).

fof(f414,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    inference(subsumption_resolution,[],[f413,f78])).

fof(f413,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f412,f130])).

fof(f130,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f114,f78])).

fof(f114,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f79,f91])).

fof(f412,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f404,f258])).

fof(f258,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f242,f78])).

fof(f242,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f126,f91])).

fof(f404,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f86,f132])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',t51_pre_topc)).

fof(f1641,plain,(
    ! [X3] : m1_subset_1(k9_subset_1(k2_tops_1(sK0,sK1),X3,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f746,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t68_tops_1.p',dt_k9_subset_1)).
%------------------------------------------------------------------------------
