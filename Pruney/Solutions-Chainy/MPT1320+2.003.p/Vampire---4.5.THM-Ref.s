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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 167 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  353 ( 991 expanded)
%              Number of equality atoms :   55 (  68 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(subsumption_resolution,[],[f260,f217])).

fof(f217,plain,(
    ! [X2,X3] : m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2)) ),
    inference(forward_demodulation,[],[f208,f207])).

fof(f207,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(resolution,[],[f71,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f56,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f208,plain,(
    ! [X2,X3] : m1_subset_1(k9_subset_1(X2,X3,X2),k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f260,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) ),
    inference(forward_demodulation,[],[f259,f96])).

fof(f96,plain,(
    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    & r2_hidden(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3))
                & r2_hidden(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3))
              & r2_hidden(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3))
            & r2_hidden(sK1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
          & r2_hidden(sK1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
        & r2_hidden(sK1,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).

fof(f94,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f259,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f258,f36])).

fof(f258,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f257,f38])).

fof(f257,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f256,f39])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f256,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f255,f205])).

fof(f205,plain,(
    ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(superposition,[],[f41,f80])).

fof(f80,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2) ),
    inference(resolution,[],[f58,f38])).

fof(f41,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f255,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f245,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f245,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f113,f80])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_tops_2(X0,X1,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f112,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_tops_2(X0,X1,sK3))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f40])).

fof(f40,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ r2_hidden(X8,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k1_tops_2(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X0),X8,X1) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k1_tops_2(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ( ( ! [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3)
                              | ~ r2_hidden(X5,X2)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
                        & ( ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
                            & r2_hidden(sK5(X0,X1,X2,X3),X2)
                            & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) )
                          | r2_hidden(sK4(X0,X1,X2,X3),X3) )
                        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X7] :
                          ( ( ( r2_hidden(X7,X3)
                              | ! [X8] :
                                  ( k9_subset_1(u1_struct_0(X0),X8,X1) != X7
                                  | ~ r2_hidden(X8,X2)
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
                                & r2_hidden(sK6(X0,X1,X2,X7),X2)
                                & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X7,X3) ) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( k9_subset_1(u1_struct_0(X0),X6,X1) = X4
                & r2_hidden(X6,X2)
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
     => ( ( ! [X5] :
              ( k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
        & r2_hidden(sK5(X0,X1,X2,X3),X2)
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
        & r2_hidden(sK6(X0,X1,X2,X7),X2)
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X6] :
                                ( k9_subset_1(u1_struct_0(X0),X6,X1) = X4
                                & r2_hidden(X6,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X7] :
                          ( ( ( r2_hidden(X7,X3)
                              | ! [X8] :
                                  ( k9_subset_1(u1_struct_0(X0),X8,X1) != X7
                                  | ~ r2_hidden(X8,X2)
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X9] :
                                  ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
                                  & r2_hidden(X9,X2)
                                  & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X7,X3) ) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                & r2_hidden(X5,X2)
                                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ! [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                  | ~ r2_hidden(X5,X2)
                                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                  & r2_hidden(X5,X2)
                                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                & r2_hidden(X5,X2)
                                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ! [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                  | ~ r2_hidden(X5,X2)
                                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                  & r2_hidden(X5,X2)
                                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:23:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (21820)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (21840)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (21828)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (21821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (21819)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (21822)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21842)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (21833)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (21828)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (21818)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (21844)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f260,f217])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X2))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f208,f207])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f71,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f56,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    ( ! [X2,X3] : (m1_subset_1(k9_subset_1(X2,X3,X2),k1_zfmisc_1(X2))) )),
% 0.22/0.51    inference(resolution,[],[f71,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f259,f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f94,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    (((~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24,f23,f22,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f42,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.22/0.51    inference(subsumption_resolution,[],[f258,f36])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f257,f38])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f256,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f255,f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 0.22/0.51    inference(superposition,[],[f41,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f58,f38])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f245,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(superposition,[],[f113,f80])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_tops_2(X0,X1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_tops_2(X0,X1,sK3)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(k1_tops_2(X0,X1,sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(resolution,[],[f62,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    r2_hidden(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X8,X1] : (~r2_hidden(X8,X2) | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f31,f30,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X7,X2,X1,X0] : (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(rectify,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : (((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21828)------------------------------
% 0.22/0.51  % (21828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21828)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21828)Memory used [KB]: 10746
% 0.22/0.51  % (21828)Time elapsed: 0.103 s
% 0.22/0.51  % (21828)------------------------------
% 0.22/0.51  % (21828)------------------------------
% 0.22/0.51  % (21824)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (21814)Success in time 0.149 s
%------------------------------------------------------------------------------
