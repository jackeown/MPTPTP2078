%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t34_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:28 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 282 expanded)
%              Number of leaves         :   11 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :  190 (1570 expanded)
%              Number of equality atoms :   40 ( 309 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(subsumption_resolution,[],[f815,f485])).

fof(f485,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(X2,sK2),k2_pre_topc(sK0,k3_xboole_0(X2,sK2))) ),
    inference(subsumption_resolution,[],[f472,f75])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f66,f65,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2))
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2))
            & v4_pre_topc(X2,X0)
            & v4_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
          & v4_pre_topc(X2,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2))
        & v4_pre_topc(sK2,X0)
        & v4_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',t34_tops_1)).

fof(f472,plain,(
    ! [X2] :
      ( r1_tarski(k3_xboole_0(X2,sK2),k2_pre_topc(sK0,k3_xboole_0(X2,sK2)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f401,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',t48_pre_topc)).

fof(f401,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f77,f313])).

fof(f313,plain,(
    ! [X1] :
      ( m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f103,f161])).

fof(f161,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2) = k3_xboole_0(X2,sK2) ),
    inference(resolution,[],[f77,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',redefinition_k9_subset_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',dt_k9_subset_1)).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f815,plain,(
    ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f814,f309])).

fof(f309,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f161,f238])).

fof(f238,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f216,f168])).

fof(f168,plain,(
    k2_pre_topc(sK0,sK2) = sK2 ),
    inference(subsumption_resolution,[],[f167,f75])).

fof(f167,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f157,f79])).

fof(f79,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f157,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | k2_pre_topc(sK0,sK2) = sK2
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f77,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',t52_pre_topc)).

fof(f216,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f127,f80])).

fof(f80,plain,(
    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f67])).

fof(f127,plain,(
    k2_pre_topc(sK0,sK1) = sK1 ),
    inference(subsumption_resolution,[],[f126,f75])).

fof(f126,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f116,f78])).

fof(f78,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f116,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f85])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f814,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f639,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',d10_xboole_0)).

fof(f639,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f638,f89])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',commutativity_k3_xboole_0)).

fof(f638,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f633,f76])).

fof(f633,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f402,f127])).

fof(f402,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k3_xboole_0(sK2,k2_pre_topc(sK0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f77,f317])).

fof(f317,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k3_xboole_0(sK2,k2_pre_topc(sK0,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f316,f89])).

fof(f316,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k3_xboole_0(k2_pre_topc(sK0,X0),sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f315,f161])).

fof(f315,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f314,f168])).

fof(f314,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f312,f75])).

fof(f312,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f86,f161])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t34_tops_1.p',t51_pre_topc)).
%------------------------------------------------------------------------------
