%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (4691 expanded)
%              Number of leaves         :   14 (1450 expanded)
%              Depth                    :   42
%              Number of atoms          :  636 (39902 expanded)
%              Number of equality atoms :   77 ( 744 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(subsumption_resolution,[],[f288,f271])).

fof(f271,plain,(
    ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f264,f88])).

fof(f88,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f47,f85])).

fof(f85,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f84,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(f84,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f83,f70])).

fof(f70,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f43,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f73,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f264,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f263,f87])).

fof(f87,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f46,f85])).

fof(f46,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f263,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f262,f148])).

% (31137)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f148,plain,(
    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f147,f39])).

fof(f147,plain,
    ( k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f146,f40])).

fof(f40,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

% (31136)Refutation not found, incomplete strategy% (31136)------------------------------
% (31136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31136)Termination reason: Refutation not found, incomplete strategy

% (31136)Memory used [KB]: 10746
% (31136)Time elapsed: 0.116 s
% (31136)------------------------------
% (31136)------------------------------
fof(f146,plain,
    ( k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f145,f41])).

fof(f41,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f145,plain,
    ( k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f144,plain,
    ( k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f43])).

fof(f136,plain,
    ( k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f135,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f135,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f134,f39])).

fof(f134,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f133,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f86,f61])).

% (31130)Refutation not found, incomplete strategy% (31130)------------------------------
% (31130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31130)Termination reason: Refutation not found, incomplete strategy

% (31130)Memory used [KB]: 1791
% (31130)Time elapsed: 0.111 s
% (31130)------------------------------
% (31130)------------------------------
fof(f86,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f74,f85])).

fof(f74,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f262,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f261,f39])).

fof(f261,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f40])).

fof(f260,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f259,f41])).

fof(f259,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f42])).

fof(f258,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f257,f43])).

fof(f257,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f135])).

fof(f256,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f255,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f246])).

fof(f246,plain,(
    sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(subsumption_resolution,[],[f245,f212])).

fof(f212,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f211,f88])).

fof(f211,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f197,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f197,plain,
    ( r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    inference(resolution,[],[f178,f44])).

fof(f178,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | r2_hidden(X5,k2_orders_2(sK0,k1_tarski(sK2))) ) ),
    inference(forward_demodulation,[],[f177,f148])).

fof(f177,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2))) ) ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f40])).

fof(f175,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f41])).

fof(f174,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f42])).

fof(f173,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f141,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f135,f65])).

fof(f65,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f245,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(superposition,[],[f223,f214])).

fof(f214,plain,
    ( sK1 = sK4(sK1,sK0,k1_tarski(sK2))
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f211,f160])).

fof(f160,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1 ) ),
    inference(forward_demodulation,[],[f159,f148])).

fof(f159,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1 ) ),
    inference(subsumption_resolution,[],[f158,f39])).

fof(f158,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f40])).

fof(f157,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f41])).

fof(f156,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f42])).

fof(f155,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f138,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f135,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sK4(X0,X1,X2) = X0
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f223,plain,
    ( r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f218,f68])).

% (31128)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f68,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f218,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f207,f45])).

fof(f207,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k1_tarski(sK2))
      | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),X0)
      | r2_orders_2(sK0,sK1,sK2) ) ),
    inference(resolution,[],[f166,f87])).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK0,k1_tarski(sK2)))
      | ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) ) ),
    inference(forward_demodulation,[],[f165,f148])).

fof(f165,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) ) ),
    inference(subsumption_resolution,[],[f164,f39])).

fof(f164,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f40])).

fof(f163,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f41])).

fof(f162,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f42])).

fof(f161,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f139,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f135,f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_orders_2(X1,sK4(X0,X1,X2),X6)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

% (31141)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f288,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f223,f275])).

fof(f275,plain,(
    sK1 = sK4(sK1,sK0,k1_tarski(sK2)) ),
    inference(resolution,[],[f264,f160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (31130)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (31148)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (31140)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (31134)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (31132)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31126)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (31131)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (31129)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (31138)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (31140)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (31127)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (31136)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f288,f271])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f264,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f47,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    (((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X2] : ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    l1_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    l1_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f73,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.21/0.53    inference(resolution,[],[f45,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f263,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f46,f85])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f262,f148])).
% 0.21/0.53  % (31137)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f39])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v3_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  % (31136)Refutation not found, incomplete strategy% (31136)------------------------------
% 0.21/0.53  % (31136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31136)Memory used [KB]: 10746
% 0.21/0.53  % (31136)Time elapsed: 0.116 s
% 0.21/0.53  % (31136)------------------------------
% 0.21/0.53  % (31136)------------------------------
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v4_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v5_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f136,f43])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f135,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f134,f39])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f70])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f86,f61])).
% 0.21/0.53  % (31130)Refutation not found, incomplete strategy% (31130)------------------------------
% 0.21/0.53  % (31130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31130)Memory used [KB]: 1791
% 0.21/0.53  % (31130)Time elapsed: 0.111 s
% 0.21/0.53  % (31130)------------------------------
% 0.21/0.53  % (31130)------------------------------
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(backward_demodulation,[],[f74,f85])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f45,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f261,f39])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f260,f40])).
% 0.21/0.54  fof(f260,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f259,f41])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f258,f42])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f257,f43])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f256,f135])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f255,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(superposition,[],[f64,f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f245,f212])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ~r2_orders_2(sK0,sK1,sK2) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.54    inference(resolution,[],[f211,f88])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.54    inference(resolution,[],[f197,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2)) | r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))),
% 0.21/0.54    inference(resolution,[],[f178,f44])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | r2_hidden(X5,k2_orders_2(sK0,k1_tarski(sK2)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f177,f148])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f176,f39])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2))) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f175,f40])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f174,f41])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f173,f42])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f43])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(sK3(sK0,k1_tarski(sK2),X5),k1_tarski(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f135,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.54    inference(rectify,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    r2_orders_2(sK0,sK1,sK2) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f243])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    r2_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK1,sK2) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.54    inference(superposition,[],[f223,f214])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    sK1 = sK4(sK1,sK0,k1_tarski(sK2)) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.54    inference(resolution,[],[f211,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1) )),
% 0.21/0.54    inference(forward_demodulation,[],[f159,f148])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f158,f39])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1 | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f157,f40])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f156,f41])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f155,f42])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f138,f43])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f135,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sK4(X0,X1,X2) = X0 | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f218,f68])).
% 0.21/0.54  % (31128)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.54    inference(equality_resolution,[],[f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.54    inference(equality_resolution,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    ~r2_hidden(sK2,k1_tarski(sK2)) | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f207,f45])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tarski(sK2)) | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),X0) | r2_orders_2(sK0,sK1,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f166,f87])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k2_orders_2(sK0,k1_tarski(sK2))) | ~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f165,f148])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f164,f39])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f163,f40])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f41])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f161,f42])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f139,f43])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f135,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) | r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK3(X1,X2,X3)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  % (31141)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    r2_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.54    inference(backward_demodulation,[],[f223,f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    sK1 = sK4(sK1,sK0,k1_tarski(sK2))),
% 0.21/0.54    inference(resolution,[],[f264,f160])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31140)------------------------------
% 0.21/0.54  % (31140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31140)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31140)Memory used [KB]: 1918
% 0.21/0.54  % (31140)Time elapsed: 0.071 s
% 0.21/0.54  % (31140)------------------------------
% 0.21/0.54  % (31140)------------------------------
% 0.21/0.54  % (31135)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (31146)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (31145)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (31125)Success in time 0.173 s
%------------------------------------------------------------------------------
