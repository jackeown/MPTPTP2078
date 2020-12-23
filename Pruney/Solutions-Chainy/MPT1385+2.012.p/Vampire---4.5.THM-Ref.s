%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 (2986 expanded)
%              Number of leaves         :   18 ( 924 expanded)
%              Depth                    :   54
%              Number of atoms          :  532 (19748 expanded)
%              Number of equality atoms :   15 ( 333 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f177])).

fof(f177,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f176,f81])).

fof(f81,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f53,f80])).

fof(f80,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f58,f78])).

fof(f78,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f53,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f175,f80])).

% (23258)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (23261)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f175,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f174,f82])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f54,f80])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f173,f80])).

fof(f173,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f172,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f172,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f171,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f171,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f52])).

fof(f170,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f62,f137])).

fof(f137,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f57])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f136,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f135,f126])).

fof(f126,plain,(
    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f124,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f66,f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f124,plain,(
    r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f119,f109])).

fof(f109,plain,(
    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f108,f81])).

fof(f108,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f107,f80])).

fof(f107,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f106,f80])).

fof(f106,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f105,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f103,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f69,f98])).

fof(f98,plain,(
    m1_connsp_2(sK3(sK0,sK1),sK0,sK1) ),
    inference(resolution,[],[f97,f81])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_connsp_2(sK3(sK0,X0),sK0,X0) ) ),
    inference(subsumption_resolution,[],[f96,f50])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_connsp_2(sK3(sK0,X0),sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f51])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_connsp_2(sK3(sK0,X0),sK0,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f52])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_connsp_2(sK3(sK0,X0),sK0,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f70,f80])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK3(X0,X1),X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK3(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK3(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(X0))
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f118,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f118,plain,(
    r2_hidden(sK1,sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f117,f109])).

fof(f117,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | r2_hidden(sK1,sK3(sK0,sK1)) ),
    inference(forward_demodulation,[],[f116,f80])).

fof(f116,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f115,f81])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f114,f80])).

fof(f114,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f51])).

fof(f112,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f52])).

fof(f111,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f63,f98])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f135,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f134,f80])).

fof(f134,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f133,f82])).

fof(f133,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f132,f80])).

fof(f132,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f131,f51])).

fof(f131,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f130,f52])).

fof(f130,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f64,f92])).

fof(f92,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f83,f90])).

fof(f90,plain,(
    k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f89,f50])).

fof(f89,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f88,f78])).

fof(f88,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f86,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f75,f81])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f57])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f83,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(k2_struct_0(sK0),sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f55,f80])).

fof(f55,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_connsp_2(X2,X0,X1)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f217,plain,(
    ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f216,f91])).

fof(f91,plain,
    ( ~ m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f84,f90])).

fof(f84,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(k2_struct_0(sK0),sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f56,f80])).

fof(f56,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f216,plain,(
    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f215,f126])).

fof(f215,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) ),
    inference(forward_demodulation,[],[f214,f80])).

fof(f214,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f213,f82])).

fof(f213,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f212,f80])).

fof(f212,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f211,f51])).

fof(f211,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f210,f52])).

fof(f210,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f205,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f205,plain,(
    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f187,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f73,f57])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f187,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f186,f81])).

fof(f186,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f185,f80])).

fof(f185,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f184,f82])).

fof(f184,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f183,f80])).

fof(f183,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f182,f50])).

fof(f182,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f181,f51])).

fof(f181,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f52])).

fof(f178,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f177,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:55:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (23254)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (23267)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (23268)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (23259)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (23260)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (23264)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (23257)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (23256)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (23267)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f217,f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f176,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.49    inference(backward_demodulation,[],[f53,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f58,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f59,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f15])).
% 0.20/0.49  fof(f15,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k2_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(forward_demodulation,[],[f175,f80])).
% 0.20/0.50  % (23258)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (23261)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f174,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f54,f80])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f173,f80])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f172,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f171,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f170,f52])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f62,f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f136,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f72,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f135,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    inference(resolution,[],[f124,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f66,f57])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f119,f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f108,f81])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k2_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f107,f80])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f106,f80])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f50])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f104,f51])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f52])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f69,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    m1_connsp_2(sK3(sK0,sK1),sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f97,f81])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_connsp_2(sK3(sK0,X0),sK0,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f96,f50])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_connsp_2(sK3(sK0,X0),sK0,X0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f95,f51])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_connsp_2(sK3(sK0,X0),sK0,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f52])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | m1_connsp_2(sK3(sK0,X0),sK0,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(superposition,[],[f70,f80])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK3(X0,X1),X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_connsp_2(sK3(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK3(X0,X1),X0,X1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(X0)) | r2_hidden(sK1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f118,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    r2_hidden(sK1,sK3(sK0,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f117,f109])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK1,sK3(sK0,sK1))),
% 0.20/0.51    inference(forward_demodulation,[],[f116,f80])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f81])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k2_struct_0(sK0)) | r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f114,f80])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f50])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f112,f51])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f52])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f63,f98])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(forward_demodulation,[],[f134,f80])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f133,f82])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(forward_demodulation,[],[f132,f80])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f131,f51])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f130,f52])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f64,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(backward_demodulation,[],[f83,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f89,f50])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f88,f78])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f86,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    v1_xboole_0(k2_struct_0(sK0)) | k6_domain_1(k2_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.51    inference(resolution,[],[f75,f81])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f68,f57])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k6_domain_1(k2_struct_0(sK0),sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(backward_demodulation,[],[f55,f80])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m2_connsp_2(X2,X0,X1) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ~m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f216,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(backward_demodulation,[],[f84,f90])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~m2_connsp_2(sK2,sK0,k6_domain_1(k2_struct_0(sK0),sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(backward_demodulation,[],[f56,f80])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f215,f126])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.20/0.51    inference(forward_demodulation,[],[f214,f80])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f213,f82])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f212,f80])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f211,f51])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f210,f52])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f205,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(resolution,[],[f187,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f73,f57])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f186,f81])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k2_struct_0(sK0)) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f185,f80])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f184,f82])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f183,f80])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f182,f50])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f181,f51])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f178,f52])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f177,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f45])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (23267)------------------------------
% 0.20/0.51  % (23267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23267)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (23267)Memory used [KB]: 1663
% 0.20/0.51  % (23267)Time elapsed: 0.071 s
% 0.20/0.51  % (23267)------------------------------
% 0.20/0.51  % (23267)------------------------------
% 0.20/0.51  % (23269)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (23253)Success in time 0.151 s
%------------------------------------------------------------------------------
