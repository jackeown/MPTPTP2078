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
% DateTime   : Thu Dec  3 13:13:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 392 expanded)
%              Number of leaves         :   14 ( 151 expanded)
%              Depth                    :   19
%              Number of atoms          :  257 (2234 expanded)
%              Number of equality atoms :   44 ( 383 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f167,f79])).

fof(f79,plain,(
    ~ v3_pre_topc(sK1,sK2) ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f47,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v3_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

% (16118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f26,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v3_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f48,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,(
    v3_pre_topc(sK1,sK2) ),
    inference(forward_demodulation,[],[f166,f134])).

fof(f134,plain,(
    sK1 = k3_xboole_0(sK1,k2_struct_0(sK2)) ),
    inference(resolution,[],[f112,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f112,plain,(
    r1_tarski(sK1,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f86,f109])).

fof(f109,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f92,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f92,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f86,plain,(
    r1_tarski(sK1,u1_struct_0(sK2)) ),
    inference(resolution,[],[f72,f80])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f166,plain,(
    v3_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f165,f156])).

fof(f156,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_subset_1(X0,X1,X0) ),
    inference(resolution,[],[f88,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f73,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f165,plain,(
    v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f164,f113])).

fof(f113,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f80,f109])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f158,f134])).

fof(f158,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(backward_demodulation,[],[f144,f156])).

fof(f144,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)
    | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f143,f109])).

fof(f143,plain,
    ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f142,f109])).

fof(f142,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f129,f44])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0) ) ),
    inference(subsumption_resolution,[],[f128,f83])).

fof(f83,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f43,f82])).

fof(f82,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f81,f49])).

fof(f81,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f42])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f127,f82])).

fof(f127,plain,(
    ! [X0] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f126,f42])).

fof(f126,plain,(
    ! [X0] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_pre_topc(X3,X0)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK7(X0,X1,X2),X0)
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK7(X0,X1,X2),X0)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (16108)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (16100)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (16100)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~v3_pre_topc(sK1,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f48,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    sK1 = sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    (((~v3_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26,f25,f24,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v3_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  % (16118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X3] : (~v3_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v3_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v3_pre_topc(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    v3_pre_topc(sK1,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f166,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    sK1 = k3_xboole_0(sK1,k2_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f112,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    r1_tarski(sK1,k2_struct_0(sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f86,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.50    inference(resolution,[],[f92,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    l1_struct_0(sK2)),
% 0.21/0.50    inference(resolution,[],[f85,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    l1_pre_topc(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f61,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    r1_tarski(sK1,u1_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f72,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.50    inference(forward_demodulation,[],[f46,f47])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    v3_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f165,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_subset_1(X0,X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f88,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f73,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.50    inference(backward_demodulation,[],[f80,f109])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f158,f134])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~m1_subset_1(k3_xboole_0(sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f144,f156])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.50    inference(forward_demodulation,[],[f143,f109])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f142,f109])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.50    inference(resolution,[],[f129,f44])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f128,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f43,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f81,f49])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f50,f42])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f127,f82])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f126,f42])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f76,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v3_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~v3_pre_topc(X3,X0) | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK7(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(rectify,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16100)------------------------------
% 0.21/0.50  % (16100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16100)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16100)Memory used [KB]: 1791
% 0.21/0.50  % (16100)Time elapsed: 0.093 s
% 0.21/0.50  % (16100)------------------------------
% 0.21/0.50  % (16100)------------------------------
% 0.21/0.51  % (16092)Success in time 0.149 s
%------------------------------------------------------------------------------
