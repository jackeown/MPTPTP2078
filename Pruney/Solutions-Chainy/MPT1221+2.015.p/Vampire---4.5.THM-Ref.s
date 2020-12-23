%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 581 expanded)
%              Number of leaves         :   11 ( 164 expanded)
%              Depth                    :   24
%              Number of atoms          :  256 (2959 expanded)
%              Number of equality atoms :   21 (  84 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(subsumption_resolution,[],[f237,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (17973)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f23,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f237,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f221,f236])).

fof(f236,plain,(
    ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f220,f30])).

fof(f220,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f208,f59])).

fof(f59,plain,(
    ! [X6] :
      ( r1_tarski(sK1,X6)
      | ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,X6),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK2(X0,X1,X2),X2)
            & r2_hidden(sK2(X0,X1,X2),X1)
            & m1_subset_1(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f208,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f207,f204])).

fof(f204,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f203,f31])).

% (17987)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f31,plain,
    ( v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f203,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f202,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f202,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f198,f30])).

fof(f198,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f35,f193])).

fof(f193,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f189,f30])).

fof(f189,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f63])).

fof(f63,plain,(
    ! [X10] :
      ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X10))
      | ~ r1_tarski(sK1,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f102,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f101,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f30])).

fof(f100,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f54,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f99,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f37,f69])).

fof(f69,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f53,f46])).

fof(f53,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
      | ~ r1_xboole_0(X1,X2)
      | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f207,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f206,f32])).

fof(f32,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f206,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f205,f29])).

fof(f205,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f199,f30])).

fof(f199,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f36,f193])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f221,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f208,f57])).

fof(f57,plain,(
    ! [X4] :
      ( r1_tarski(sK1,X4)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1,X4),sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (17980)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (17975)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (17974)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (17972)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (17970)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (17979)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (17992)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (17980)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (17984)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (17969)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (17971)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (17982)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (17990)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (17979)Refutation not found, incomplete strategy% (17979)------------------------------
% 0.22/0.53  % (17979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17979)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17979)Memory used [KB]: 10618
% 0.22/0.53  % (17979)Time elapsed: 0.097 s
% 0.22/0.53  % (17979)------------------------------
% 0.22/0.53  % (17979)------------------------------
% 0.22/0.53  % (17972)Refutation not found, incomplete strategy% (17972)------------------------------
% 0.22/0.53  % (17972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17972)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17972)Memory used [KB]: 10490
% 0.22/0.53  % (17972)Time elapsed: 0.110 s
% 0.22/0.53  % (17972)------------------------------
% 0.22/0.53  % (17972)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f237,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  % (17973)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f221,f236])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f220,f30])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(resolution,[],[f208,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X6] : (r1_tarski(sK1,X6) | ~r2_hidden(sK2(u1_struct_0(sK0),sK1,X6),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(resolution,[],[f30,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ~r1_tarski(sK1,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f207,f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f203,f31])).
% 0.22/0.53  % (17987)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    v4_pre_topc(sK1,sK0) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f202,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f198,f30])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.53    inference(superposition,[],[f35,f193])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~r1_tarski(sK1,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f189,f30])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f102,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X10] : (r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X10)) | ~r1_tarski(sK1,X10) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(resolution,[],[f30,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f101,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    l1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f29,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f100,f30])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f30,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(superposition,[],[f37,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f53,f46])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f30,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | ~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | ~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | (~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f206,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f205,f29])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f199,f30])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,sK1)),
% 0.22/0.54    inference(superposition,[],[f36,f193])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f208,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X4] : (r1_tarski(sK1,X4) | r2_hidden(sK2(u1_struct_0(sK0),sK1,X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(resolution,[],[f30,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (17980)------------------------------
% 0.22/0.54  % (17980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17980)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (17980)Memory used [KB]: 1791
% 0.22/0.54  % (17980)Time elapsed: 0.111 s
% 0.22/0.54  % (17980)------------------------------
% 0.22/0.54  % (17980)------------------------------
% 0.22/0.54  % (17992)Refutation not found, incomplete strategy% (17992)------------------------------
% 0.22/0.54  % (17992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17992)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17992)Memory used [KB]: 10618
% 0.22/0.54  % (17992)Time elapsed: 0.067 s
% 0.22/0.54  % (17992)------------------------------
% 0.22/0.54  % (17992)------------------------------
% 0.22/0.54  % (17968)Success in time 0.175 s
%------------------------------------------------------------------------------
