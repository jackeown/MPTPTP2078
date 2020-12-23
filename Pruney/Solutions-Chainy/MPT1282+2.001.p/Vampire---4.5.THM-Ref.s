%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 195 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   19
%              Number of atoms          :  177 ( 914 expanded)
%              Number of equality atoms :   56 ( 352 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f73])).

% (27642)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f73,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f42,f72])).

fof(f72,plain,(
    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) )
    & v6_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
            & v6_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1) )
          & v6_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1) )
        & v6_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) )
      & v6_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
             => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
                & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

% (27630)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
           => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tops_1)).

fof(f71,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f70,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(f59,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f58,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f56,f27])).

fof(f56,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f55,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f30,f53])).

fof(f53,plain,(
    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f52,f27])).

fof(f52,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f51,f28])).

fof(f28,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v6_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).

fof(f42,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f86,f62])).

fof(f62,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f60,f53])).

fof(f60,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f48,f27])).

fof(f48,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f47,f26])).

fof(f47,plain,(
    ! [X0] :
      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

% (27637)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f86,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f84,f27])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:42:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (27634)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (27634)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f73])).
% 0.21/0.50  % (27642)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f42,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f71,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ((k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)) & v6_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1)) & v6_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X1] : ((k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1)) & v6_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)) & v6_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) => (k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  % (27630)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) => (k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tops_1)).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f59,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f58,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f26])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f56,f27])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f55,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f54,f26])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(superposition,[],[f30,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f52,f27])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f51,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v6_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~v6_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.50    inference(resolution,[],[f33,f26])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(inner_rewriting,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f86,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    sK1 = k1_tops_1(sK0,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f60,f53])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f48,f27])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f47,f26])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f45,f35])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0))) )),
% 0.21/0.50    inference(resolution,[],[f36,f26])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  % (27637)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f84,f27])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.21/0.50    inference(resolution,[],[f32,f26])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27634)------------------------------
% 0.21/0.50  % (27634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27634)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27634)Memory used [KB]: 6140
% 0.21/0.50  % (27634)Time elapsed: 0.087 s
% 0.21/0.50  % (27634)------------------------------
% 0.21/0.50  % (27634)------------------------------
% 0.21/0.50  % (27627)Success in time 0.135 s
%------------------------------------------------------------------------------
