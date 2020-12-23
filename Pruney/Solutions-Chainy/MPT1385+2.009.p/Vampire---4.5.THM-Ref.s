%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 (2165 expanded)
%              Number of leaves         :   19 ( 660 expanded)
%              Depth                    :   46
%              Number of atoms          :  510 (14504 expanded)
%              Number of equality atoms :   33 ( 301 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1032,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1031,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f1031,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1030,f88])).

fof(f88,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1030,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1029,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1029,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1026,f994])).

fof(f994,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f993,f53])).

fof(f993,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f992,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f992,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f991,f55])).

fof(f991,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f990,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f990,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f985,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f985,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f984])).

fof(f984,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f66,f548])).

fof(f548,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f547,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f79,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f547,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f546,f241])).

fof(f241,plain,
    ( m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f110,f238])).

fof(f238,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f237,f53])).

fof(f237,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f88])).

fof(f236,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f218,f64])).

fof(f218,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f110,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f546,plain,
    ( ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f545,f54])).

fof(f545,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f544,f55])).

fof(f544,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f543,f57])).

fof(f543,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f67,f239])).

fof(f239,plain,
    ( m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f58,f238])).

fof(f58,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_connsp_2(X2,X0,X1)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f1026,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f1025,f240])).

fof(f240,plain,
    ( ~ m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f59,f238])).

fof(f59,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f1025,plain,
    ( m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1024,f241])).

fof(f1024,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1023,f54])).

fof(f1023,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1022,f55])).

fof(f1022,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1020,f57])).

fof(f1020,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f1015,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1015,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f1013,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1013,plain,
    ( m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1012,f851])).

fof(f851,plain,(
    k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f850,f53])).

fof(f850,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f849,f88])).

fof(f849,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f848,f64])).

fof(f848,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f847,f843])).

fof(f843,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f838,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f838,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f837,f53])).

fof(f837,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f836,f54])).

fof(f836,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f835,f55])).

fof(f835,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f834,f56])).

fof(f834,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f833,f57])).

fof(f833,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f65,f557])).

fof(f557,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f555,f554])).

fof(f554,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f548,f69])).

fof(f555,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f553,f83])).

fof(f553,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f548,f100])).

fof(f100,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f78,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f847,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f845])).

fof(f845,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f842,f83])).

fof(f842,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f838,f100])).

fof(f1012,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(k1_tops_1(sK0,sK2),sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f1011,f1007])).

fof(f1007,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f1001,f69])).

fof(f1001,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1000,f53])).

fof(f1000,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f999,f54])).

fof(f999,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f998,f55])).

fof(f998,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f997,f56])).

fof(f997,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f995,f57])).

fof(f995,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f994,f65])).

fof(f1011,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(k1_tops_1(sK0,sK2),sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f1006,f73])).

fof(f1006,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f1001,f100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (18414)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.44  % (18401)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.44  % (18414)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f1032,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f1031,f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f17])).
% 0.21/0.44  fof(f17,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.21/0.44  fof(f1031,plain,(
% 0.21/0.44    v2_struct_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f1030,f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    l1_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f63,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f1030,plain,(
% 0.21/0.44    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f1029,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.44  fof(f1029,plain,(
% 0.21/0.44    v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f1026,f994])).
% 0.21/0.44  fof(f994,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f993,f53])).
% 0.21/0.44  fof(f993,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f992,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f992,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f991,f55])).
% 0.21/0.44  fof(f991,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f990,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f990,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f985,f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  fof(f985,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f984])).
% 0.21/0.44  fof(f984,plain,(
% 0.21/0.44    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.44    inference(resolution,[],[f66,f548])).
% 0.21/0.44  fof(f548,plain,(
% 0.21/0.44    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.44    inference(resolution,[],[f547,f86])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f79,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(flattening,[],[f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.44    inference(nnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.44  fof(f547,plain,(
% 0.21/0.44    r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(resolution,[],[f546,f241])).
% 0.21/0.44  fof(f241,plain,(
% 0.21/0.44    m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.44    inference(backward_demodulation,[],[f110,f238])).
% 0.21/0.44  fof(f238,plain,(
% 0.21/0.44    k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f237,f53])).
% 0.21/0.44  fof(f237,plain,(
% 0.21/0.44    k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f236,f88])).
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f218,f64])).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.44    inference(resolution,[],[f83,f56])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f72,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f62,f71])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f73,f56])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.45    inference(flattening,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.45  fof(f546,plain,(
% 0.21/0.45    ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f545,f54])).
% 0.21/0.45  fof(f545,plain,(
% 0.21/0.45    r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f544,f55])).
% 0.21/0.45  fof(f544,plain,(
% 0.21/0.45    r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f543,f57])).
% 0.21/0.45  fof(f543,plain,(
% 0.21/0.45    r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(resolution,[],[f67,f239])).
% 0.21/0.45  fof(f239,plain,(
% 0.21/0.45    m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(backward_demodulation,[],[f58,f238])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f43])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m2_connsp_2(X2,X0,X1) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.45  fof(f1026,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(resolution,[],[f1025,f240])).
% 0.21/0.45  fof(f240,plain,(
% 0.21/0.45    ~m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(backward_demodulation,[],[f59,f238])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f43])).
% 0.21/0.45  fof(f1025,plain,(
% 0.21/0.45    m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f1024,f241])).
% 0.21/0.45  fof(f1024,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f1023,f54])).
% 0.21/0.45  fof(f1023,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1022,f55])).
% 0.21/0.45  fof(f1022,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1020,f57])).
% 0.21/0.45  fof(f1020,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | m2_connsp_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.45    inference(resolution,[],[f1015,f68])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f45])).
% 0.21/0.45  fof(f1015,plain,(
% 0.21/0.45    r1_tarski(k1_enumset1(sK1,sK1,sK1),k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f1013,f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f1013,plain,(
% 0.21/0.45    m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(forward_demodulation,[],[f1012,f851])).
% 0.21/0.45  fof(f851,plain,(
% 0.21/0.45    k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f850,f53])).
% 0.21/0.45  fof(f850,plain,(
% 0.21/0.45    k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f849,f88])).
% 0.21/0.45  fof(f849,plain,(
% 0.21/0.45    k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f848,f64])).
% 0.21/0.45  fof(f848,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f847,f843])).
% 0.21/0.45  fof(f843,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f838,f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(rectify,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.45  fof(f838,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f837,f53])).
% 0.21/0.45  fof(f837,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f836,f54])).
% 0.21/0.45  fof(f836,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f835,f55])).
% 0.21/0.45  fof(f835,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f834,f56])).
% 0.21/0.45  fof(f834,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f833,f57])).
% 0.21/0.45  fof(f833,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(resolution,[],[f65,f557])).
% 0.21/0.45  fof(f557,plain,(
% 0.21/0.45    m1_connsp_2(sK2,sK0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f555,f554])).
% 0.21/0.45  fof(f554,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f548,f69])).
% 0.21/0.45  fof(f555,plain,(
% 0.21/0.45    m1_connsp_2(sK2,sK0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.21/0.45    inference(resolution,[],[f553,f83])).
% 0.21/0.45  fof(f553,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f548,f100])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r2_hidden(X1,X2) | m1_subset_1(X1,X2)) )),
% 0.21/0.45    inference(resolution,[],[f78,f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f61,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f847,plain,(
% 0.21/0.45    k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f845])).
% 0.21/0.45  fof(f845,plain,(
% 0.21/0.45    k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v1_xboole_0(u1_struct_0(sK0)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.21/0.45    inference(resolution,[],[f842,f83])).
% 0.21/0.45  fof(f842,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_tops_1(sK0,sK2)) | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(k1_tops_1(sK0,sK2),sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f838,f100])).
% 0.21/0.45  fof(f1012,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(k1_tops_1(sK0,sK2),sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f1011,f1007])).
% 0.21/0.45  fof(f1007,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f1001,f69])).
% 0.21/0.45  fof(f1001,plain,(
% 0.21/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f1000,f53])).
% 0.21/0.45  fof(f1000,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f999,f54])).
% 0.21/0.45  fof(f999,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f998,f55])).
% 0.21/0.45  fof(f998,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f997,f56])).
% 0.21/0.45  fof(f997,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f995,f57])).
% 0.21/0.45  fof(f995,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f994,f65])).
% 0.21/0.45  fof(f1011,plain,(
% 0.21/0.45    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(k1_tops_1(sK0,sK2),sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2))) | v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.21/0.45    inference(resolution,[],[f1006,f73])).
% 0.21/0.45  fof(f1006,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_tops_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.45    inference(resolution,[],[f1001,f100])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (18414)------------------------------
% 0.21/0.45  % (18414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18414)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (18414)Memory used [KB]: 2686
% 0.21/0.45  % (18414)Time elapsed: 0.040 s
% 0.21/0.45  % (18414)------------------------------
% 0.21/0.45  % (18414)------------------------------
% 0.21/0.45  % (18400)Success in time 0.094 s
%------------------------------------------------------------------------------
