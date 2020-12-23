%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  136 (27428 expanded)
%              Number of leaves         :   15 (9193 expanded)
%              Depth                    :   33
%              Number of atoms          :  715 (265145 expanded)
%              Number of equality atoms :  115 (2698 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f529,plain,(
    $false ),
    inference(global_subsumption,[],[f303,f518,f528])).

fof(f528,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f521,f522])).

fof(f522,plain,(
    sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f518,f323])).

fof(f323,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X2,sK0,k2_tarski(sK1,sK1)) = X2 ) ),
    inference(forward_demodulation,[],[f308,f298])).

fof(f298,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f107,f287,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f109,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f109,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
              ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
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
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
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
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(f287,plain,(
    r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f108,f165])).

fof(f165,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(forward_demodulation,[],[f160,f113])).

fof(f113,plain,(
    k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f107,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f160,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),k6_domain_1(u1_struct_0(sK0),sK1))
      | r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(resolution,[],[f94,f107])).

fof(f94,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,X5,X6),X5)
      | r2_hidden(X6,a_2_0_orders_2(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f93,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(sK0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X6,a_2_0_orders_2(sK0,X5))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f92,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(sK0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X6,a_2_0_orders_2(sK0,X5))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f91,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(sK0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X6,a_2_0_orders_2(sK0,X5))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f79,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(sK0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X6,a_2_0_orders_2(sK0,X5))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f70])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f108,plain,(
    ~ r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f46,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

fof(f107,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f42,f45,f46,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f308,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = X2 ) ),
    inference(backward_demodulation,[],[f150,f298])).

fof(f150,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | sK4(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = X2 ) ),
    inference(forward_demodulation,[],[f145,f113])).

fof(f145,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | sK4(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = X2 ) ),
    inference(resolution,[],[f86,f107])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | sK4(X0,sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f41])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X0,sK0,X1) = X0
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK4(X0,X1,X2) = X0
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f521,plain,(
    r2_orders_2(sK0,sK1,sK4(sK2,sK0,k2_tarski(sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f46,f75,f518,f354])).

fof(f354,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | r2_orders_2(sK0,X3,sK4(X4,sK0,k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X3,k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f353,f298])).

fof(f353,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X3,k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(forward_demodulation,[],[f313,f298])).

fof(f313,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k2_tarski(sK1,sK1))
      | ~ r2_hidden(X4,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(backward_demodulation,[],[f190,f298])).

fof(f190,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,k6_domain_1(u1_struct_0(sK0),sK1))
      | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(forward_demodulation,[],[f185,f113])).

fof(f185,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(X3,k6_domain_1(u1_struct_0(sK0),sK1))
      | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(resolution,[],[f90,f107])).

fof(f90,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ r2_hidden(X2,X3)
      | r2_orders_2(sK0,X2,sK4(X4,sK0,X3)) ) ),
    inference(subsumption_resolution,[],[f89,f41])).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X2,sK4(X4,sK0,X3))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X2,sK4(X4,sK0,X3))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f87,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X2,sK4(X4,sK0,X3))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X2,sK4(X4,sK0,X3))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_orders_2(X1,X6,sK4(X0,X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f518,plain,(
    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f517,f302])).

fof(f302,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f48,f298])).

fof(f48,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f517,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(backward_demodulation,[],[f358,f516])).

fof(f516,plain,(
    sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f515,f436])).

fof(f436,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f433,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f433,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f428,f303])).

fof(f428,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0)
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0) ) ),
    inference(resolution,[],[f324,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f324,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK0,k2_tarski(sK1,sK1),X2),k2_tarski(sK1,sK1))
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f309,f298])).

fof(f309,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f165,f298])).

fof(f515,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f511,f46])).

fof(f511,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(resolution,[],[f490,f73])).

fof(f73,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f490,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_tarski(sK1,sK1))
      | r2_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f489,f436])).

fof(f489,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK2)
      | ~ r2_hidden(X0,k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK1,sK2)
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ) ),
    inference(superposition,[],[f483,f437])).

fof(f437,plain,
    ( sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1))
    | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(resolution,[],[f436,f315])).

fof(f315,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1)) ),
    inference(backward_demodulation,[],[f209,f298])).

fof(f209,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK4(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f150,f48])).

fof(f483,plain,(
    ! [X2] :
      ( r2_orders_2(sK0,X2,sK4(sK2,sK0,k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X2,k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK1,sK2) ) ),
    inference(resolution,[],[f354,f302])).

fof(f358,plain,
    ( ~ r2_orders_2(sK0,sK3(sK0,k2_tarski(sK1,sK1),sK2),sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(forward_demodulation,[],[f318,f298])).

fof(f318,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK2),sK2) ),
    inference(backward_demodulation,[],[f259,f298])).

fof(f259,plain,
    ( ~ r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK2),sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f180,f47])).

fof(f180,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),X2) ) ),
    inference(forward_demodulation,[],[f175,f113])).

fof(f175,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(resolution,[],[f98,f107])).

fof(f98,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK3(sK0,X7,X8),X8)
      | r2_hidden(X8,a_2_0_orders_2(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X8,X7] :
      ( ~ r2_orders_2(sK0,sK3(sK0,X7,X8),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X8,a_2_0_orders_2(sK0,X7))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f42])).

fof(f96,plain,(
    ! [X8,X7] :
      ( ~ r2_orders_2(sK0,sK3(sK0,X7,X8),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X8,a_2_0_orders_2(sK0,X7))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X8,X7] :
      ( ~ r2_orders_2(sK0,sK3(sK0,X7,X8),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X8,a_2_0_orders_2(sK0,X7))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f44])).

fof(f80,plain,(
    ! [X8,X7] :
      ( ~ r2_orders_2(sK0,sK3(sK0,X7,X8),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X8,a_2_0_orders_2(sK0,X7))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f303,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f49,f298])).

fof(f49,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (18865)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (18891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (18859)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (18860)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (18889)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (18862)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (18872)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (18873)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (18863)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (18877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (18890)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (18887)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (18864)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (18874)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (18892)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (18884)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (18864)Refutation not found, incomplete strategy% (18864)------------------------------
% 0.20/0.55  % (18864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18868)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (18864)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18864)Memory used [KB]: 1918
% 0.20/0.55  % (18864)Time elapsed: 0.123 s
% 0.20/0.55  % (18864)------------------------------
% 0.20/0.55  % (18864)------------------------------
% 0.20/0.55  % (18876)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (18875)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (18878)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (18880)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (18866)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (18879)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (18869)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (18873)Refutation not found, incomplete strategy% (18873)------------------------------
% 0.20/0.55  % (18873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18882)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (18873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18873)Memory used [KB]: 10746
% 0.20/0.55  % (18873)Time elapsed: 0.136 s
% 0.20/0.55  % (18873)------------------------------
% 0.20/0.55  % (18873)------------------------------
% 0.20/0.55  % (18886)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (18881)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (18867)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (18892)Refutation not found, incomplete strategy% (18892)------------------------------
% 0.20/0.55  % (18892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18892)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18892)Memory used [KB]: 1663
% 0.20/0.55  % (18892)Time elapsed: 0.004 s
% 0.20/0.55  % (18892)------------------------------
% 0.20/0.55  % (18892)------------------------------
% 0.20/0.56  % (18891)Refutation not found, incomplete strategy% (18891)------------------------------
% 0.20/0.56  % (18891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18891)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18891)Memory used [KB]: 10746
% 0.20/0.56  % (18891)Time elapsed: 0.133 s
% 0.20/0.56  % (18891)------------------------------
% 0.20/0.56  % (18891)------------------------------
% 0.20/0.56  % (18870)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (18870)Refutation not found, incomplete strategy% (18870)------------------------------
% 0.20/0.56  % (18870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18870)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18870)Memory used [KB]: 10746
% 0.20/0.56  % (18870)Time elapsed: 0.153 s
% 0.20/0.56  % (18870)------------------------------
% 0.20/0.56  % (18870)------------------------------
% 0.20/0.56  % (18889)Refutation not found, incomplete strategy% (18889)------------------------------
% 0.20/0.56  % (18889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18889)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18889)Memory used [KB]: 6268
% 0.20/0.56  % (18889)Time elapsed: 0.155 s
% 0.20/0.56  % (18889)------------------------------
% 0.20/0.56  % (18889)------------------------------
% 0.20/0.56  % (18887)Refutation not found, incomplete strategy% (18887)------------------------------
% 0.20/0.56  % (18887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18888)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (18877)Refutation not found, incomplete strategy% (18877)------------------------------
% 0.20/0.56  % (18877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18877)Memory used [KB]: 10618
% 0.20/0.56  % (18877)Time elapsed: 0.137 s
% 0.20/0.56  % (18877)------------------------------
% 0.20/0.56  % (18877)------------------------------
% 0.20/0.57  % (18872)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (18890)Refutation not found, incomplete strategy% (18890)------------------------------
% 0.20/0.57  % (18890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  % (18888)Refutation not found, incomplete strategy% (18888)------------------------------
% 0.20/0.57  % (18888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18888)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (18888)Memory used [KB]: 6268
% 0.20/0.57  % (18888)Time elapsed: 0.155 s
% 0.20/0.57  % (18888)------------------------------
% 0.20/0.57  % (18888)------------------------------
% 0.20/0.57  % (18879)Refutation not found, incomplete strategy% (18879)------------------------------
% 0.20/0.57  % (18879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18890)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (18890)Memory used [KB]: 6268
% 0.20/0.57  % (18890)Time elapsed: 0.139 s
% 0.20/0.57  % (18890)------------------------------
% 0.20/0.57  % (18890)------------------------------
% 0.20/0.58  
% 0.20/0.58  % (18887)Memory used [KB]: 10746
% 0.20/0.58  % (18887)Time elapsed: 0.139 s
% 0.20/0.58  % (18887)------------------------------
% 0.20/0.58  % (18887)------------------------------
% 0.20/0.58  % (18879)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (18879)Memory used [KB]: 1791
% 0.20/0.58  % (18879)Time elapsed: 0.150 s
% 0.20/0.58  % (18879)------------------------------
% 0.20/0.58  % (18879)------------------------------
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f529,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(global_subsumption,[],[f303,f518,f528])).
% 0.20/0.58  fof(f528,plain,(
% 0.20/0.58    r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.58    inference(forward_demodulation,[],[f521,f522])).
% 0.20/0.58  fof(f522,plain,(
% 0.20/0.58    sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f518,f323])).
% 0.20/0.58  fof(f323,plain,(
% 0.20/0.58    ( ! [X2] : (~r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X2,sK0,k2_tarski(sK1,sK1)) = X2) )),
% 0.20/0.58    inference(forward_demodulation,[],[f308,f298])).
% 0.20/0.58  fof(f298,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f107,f287,f118])).
% 0.20/0.58  fof(f118,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~r2_hidden(X1,X0)) )),
% 0.20/0.58    inference(resolution,[],[f109,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f3])).
% 1.70/0.58  fof(f3,axiom,(
% 1.70/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.70/0.58  fof(f109,plain,(
% 1.70/0.58    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 1.70/0.58    inference(resolution,[],[f46,f68])).
% 1.70/0.58  fof(f68,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.70/0.58    inference(definition_unfolding,[],[f54,f50])).
% 1.70/0.58  fof(f50,plain,(
% 1.70/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f2])).
% 1.70/0.58  fof(f2,axiom,(
% 1.70/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.70/0.58  fof(f54,plain,(
% 1.70/0.58    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f21])).
% 1.70/0.58  fof(f21,plain,(
% 1.70/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.70/0.58    inference(flattening,[],[f20])).
% 1.70/0.58  fof(f20,plain,(
% 1.70/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.70/0.58    inference(ennf_transformation,[],[f6])).
% 1.70/0.58  fof(f6,axiom,(
% 1.70/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.70/0.58  fof(f46,plain,(
% 1.70/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f30,plain,(
% 1.70/0.58    (((~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 1.70/0.58  fof(f27,plain,(
% 1.70/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f28,plain,(
% 1.70/0.58    ? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f29,plain,(
% 1.70/0.58    ? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f26,plain,(
% 1.70/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.70/0.58    inference(flattening,[],[f25])).
% 1.70/0.58  fof(f25,plain,(
% 1.70/0.58    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.70/0.58    inference(nnf_transformation,[],[f13])).
% 1.70/0.58  fof(f13,plain,(
% 1.70/0.58    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.70/0.58    inference(flattening,[],[f12])).
% 1.70/0.58  fof(f12,plain,(
% 1.70/0.58    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.70/0.58    inference(ennf_transformation,[],[f10])).
% 1.70/0.58  fof(f10,negated_conjecture,(
% 1.70/0.58    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.70/0.58    inference(negated_conjecture,[],[f9])).
% 1.70/0.58  fof(f9,conjecture,(
% 1.70/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).
% 1.70/0.58  fof(f287,plain,(
% 1.70/0.58    r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.70/0.58    inference(unit_resulting_resolution,[],[f46,f108,f165])).
% 1.70/0.58  fof(f165,plain,(
% 1.70/0.58    ( ! [X2] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(forward_demodulation,[],[f160,f113])).
% 1.70/0.58  fof(f113,plain,(
% 1.70/0.58    k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.70/0.58    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f107,f52])).
% 1.70/0.58  fof(f52,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f17])).
% 1.70/0.58  fof(f17,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.58    inference(flattening,[],[f16])).
% 1.70/0.58  fof(f16,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.58    inference(ennf_transformation,[],[f4])).
% 1.70/0.58  fof(f4,axiom,(
% 1.70/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 1.70/0.58  fof(f45,plain,(
% 1.70/0.58    l1_orders_2(sK0)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f44,plain,(
% 1.70/0.58    v5_orders_2(sK0)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f43,plain,(
% 1.70/0.58    v4_orders_2(sK0)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f42,plain,(
% 1.70/0.58    v3_orders_2(sK0)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f41,plain,(
% 1.70/0.58    ~v2_struct_0(sK0)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f160,plain,(
% 1.70/0.58    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),k6_domain_1(u1_struct_0(sK0),sK1)) | r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(resolution,[],[f94,f107])).
% 1.70/0.58  fof(f94,plain,(
% 1.70/0.58    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X5,X6),X5) | r2_hidden(X6,a_2_0_orders_2(sK0,X5))) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f93,f41])).
% 1.70/0.58  fof(f93,plain,(
% 1.70/0.58    ( ! [X6,X5] : (r2_hidden(sK3(sK0,X5,X6),X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X6,a_2_0_orders_2(sK0,X5)) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f92,f42])).
% 1.70/0.58  fof(f92,plain,(
% 1.70/0.58    ( ! [X6,X5] : (r2_hidden(sK3(sK0,X5,X6),X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X6,a_2_0_orders_2(sK0,X5)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f91,f43])).
% 1.70/0.58  fof(f91,plain,(
% 1.70/0.58    ( ! [X6,X5] : (r2_hidden(sK3(sK0,X5,X6),X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X6,a_2_0_orders_2(sK0,X5)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f79,f44])).
% 1.70/0.58  fof(f79,plain,(
% 1.70/0.58    ( ! [X6,X5] : (r2_hidden(sK3(sK0,X5,X6),X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X6,a_2_0_orders_2(sK0,X5)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(resolution,[],[f45,f70])).
% 1.70/0.58  fof(f70,plain,(
% 1.70/0.58    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.70/0.58    inference(equality_resolution,[],[f59])).
% 1.70/0.58  fof(f59,plain,(
% 1.70/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f35])).
% 1.70/0.58  fof(f35,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).
% 1.70/0.58  fof(f33,plain,(
% 1.70/0.58    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f34,plain,(
% 1.70/0.58    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f32,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.70/0.58    inference(rectify,[],[f31])).
% 1.70/0.58  fof(f31,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.70/0.58    inference(nnf_transformation,[],[f23])).
% 1.70/0.58  fof(f23,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.70/0.58    inference(flattening,[],[f22])).
% 1.70/0.58  fof(f22,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.70/0.58    inference(ennf_transformation,[],[f5])).
% 1.70/0.58  fof(f5,axiom,(
% 1.70/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.70/0.58  fof(f108,plain,(
% 1.70/0.58    ~r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.70/0.58    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f46,f51])).
% 1.70/0.58  fof(f51,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f15])).
% 1.70/0.58  fof(f15,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.58    inference(flattening,[],[f14])).
% 1.70/0.58  fof(f14,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.58    inference(ennf_transformation,[],[f8])).
% 1.70/0.58  fof(f8,axiom,(
% 1.70/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).
% 1.70/0.58  fof(f107,plain,(
% 1.70/0.58    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.58    inference(unit_resulting_resolution,[],[f41,f42,f45,f46,f53])).
% 1.70/0.58  fof(f53,plain,(
% 1.70/0.58    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f19])).
% 1.70/0.58  fof(f19,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.58    inference(flattening,[],[f18])).
% 1.70/0.58  fof(f18,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.58    inference(ennf_transformation,[],[f11])).
% 1.70/0.58  fof(f11,plain,(
% 1.70/0.58    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.58    inference(pure_predicate_removal,[],[f7])).
% 1.70/0.58  fof(f7,axiom,(
% 1.70/0.58    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 1.70/0.58  fof(f308,plain,(
% 1.70/0.58    ( ! [X2] : (~r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = X2) )),
% 1.70/0.58    inference(backward_demodulation,[],[f150,f298])).
% 1.70/0.58  fof(f150,plain,(
% 1.70/0.58    ( ! [X2] : (~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | sK4(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = X2) )),
% 1.70/0.58    inference(forward_demodulation,[],[f145,f113])).
% 1.70/0.58  fof(f145,plain,(
% 1.70/0.58    ( ! [X2] : (~r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | sK4(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = X2) )),
% 1.70/0.58    inference(resolution,[],[f86,f107])).
% 1.70/0.58  fof(f86,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | sK4(X0,sK0,X1) = X0) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f85,f41])).
% 1.70/0.58  fof(f85,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f84,f42])).
% 1.70/0.58  fof(f84,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f83,f43])).
% 1.70/0.58  fof(f83,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f77,f44])).
% 1.70/0.58  fof(f77,plain,(
% 1.70/0.58    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X0,sK0,X1) = X0 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(resolution,[],[f45,f56])).
% 1.70/0.58  fof(f56,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X1) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK4(X0,X1,X2) = X0 | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f35])).
% 1.70/0.58  fof(f521,plain,(
% 1.70/0.58    r2_orders_2(sK0,sK1,sK4(sK2,sK0,k2_tarski(sK1,sK1)))),
% 1.70/0.58    inference(unit_resulting_resolution,[],[f46,f75,f518,f354])).
% 1.70/0.58  fof(f354,plain,(
% 1.70/0.58    ( ! [X4,X3] : (~r2_hidden(X4,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | r2_orders_2(sK0,X3,sK4(X4,sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X3,k2_tarski(sK1,sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 1.70/0.58    inference(forward_demodulation,[],[f353,f298])).
% 1.70/0.58  fof(f353,plain,(
% 1.70/0.58    ( ! [X4,X3] : (~r2_hidden(X4,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X3,k2_tarski(sK1,sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(forward_demodulation,[],[f313,f298])).
% 1.70/0.58  fof(f313,plain,(
% 1.70/0.58    ( ! [X4,X3] : (~r2_hidden(X3,k2_tarski(sK1,sK1)) | ~r2_hidden(X4,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(backward_demodulation,[],[f190,f298])).
% 1.70/0.58  fof(f190,plain,(
% 1.70/0.58    ( ! [X4,X3] : (~r2_hidden(X4,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,k6_domain_1(u1_struct_0(sK0),sK1)) | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(forward_demodulation,[],[f185,f113])).
% 1.70/0.58  fof(f185,plain,(
% 1.70/0.58    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(X3,k6_domain_1(u1_struct_0(sK0),sK1)) | r2_orders_2(sK0,X3,sK4(X4,sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(resolution,[],[f90,f107])).
% 1.70/0.58  fof(f90,plain,(
% 1.70/0.58    ( ! [X4,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~r2_hidden(X2,X3) | r2_orders_2(sK0,X2,sK4(X4,sK0,X3))) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f89,f41])).
% 1.70/0.58  fof(f89,plain,(
% 1.70/0.58    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X2,sK4(X4,sK0,X3)) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f88,f42])).
% 1.70/0.58  fof(f88,plain,(
% 1.70/0.58    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X2,sK4(X4,sK0,X3)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f87,f43])).
% 1.70/0.58  fof(f87,plain,(
% 1.70/0.58    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X2,sK4(X4,sK0,X3)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f78,f44])).
% 1.70/0.58  fof(f78,plain,(
% 1.70/0.58    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X2,sK4(X4,sK0,X3)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(resolution,[],[f45,f57])).
% 1.70/0.58  fof(f57,plain,(
% 1.70/0.58    ( ! [X6,X2,X0,X1] : (~l1_orders_2(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f35])).
% 1.70/0.58  fof(f75,plain,(
% 1.70/0.58    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.70/0.58    inference(equality_resolution,[],[f74])).
% 1.70/0.58  fof(f74,plain,(
% 1.70/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.70/0.58    inference(equality_resolution,[],[f62])).
% 1.70/0.58  fof(f62,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.70/0.58    inference(cnf_transformation,[],[f40])).
% 1.70/0.58  fof(f40,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.70/0.58  fof(f39,plain,(
% 1.70/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f38,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.58    inference(rectify,[],[f37])).
% 1.70/0.58  fof(f37,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.58    inference(flattening,[],[f36])).
% 1.70/0.58  fof(f36,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.58    inference(nnf_transformation,[],[f1])).
% 1.70/0.58  fof(f1,axiom,(
% 1.70/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.70/0.58  fof(f518,plain,(
% 1.70/0.58    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 1.70/0.58    inference(subsumption_resolution,[],[f517,f302])).
% 1.70/0.58  fof(f302,plain,(
% 1.70/0.58    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | r2_orders_2(sK0,sK1,sK2)),
% 1.70/0.58    inference(backward_demodulation,[],[f48,f298])).
% 1.70/0.58  fof(f48,plain,(
% 1.70/0.58    r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f517,plain,(
% 1.70/0.58    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 1.70/0.58    inference(backward_demodulation,[],[f358,f516])).
% 1.70/0.58  fof(f516,plain,(
% 1.70/0.58    sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)),
% 1.70/0.58    inference(subsumption_resolution,[],[f515,f436])).
% 1.70/0.58  fof(f436,plain,(
% 1.70/0.58    ~r2_orders_2(sK0,sK1,sK2) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)),
% 1.70/0.58    inference(subsumption_resolution,[],[f433,f47])).
% 1.70/0.58  fof(f47,plain,(
% 1.70/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  fof(f433,plain,(
% 1.70/0.58    ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.70/0.58    inference(resolution,[],[f428,f303])).
% 1.70/0.58  fof(f428,plain,(
% 1.70/0.58    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0)) )),
% 1.70/0.58    inference(duplicate_literal_removal,[],[f426])).
% 1.70/0.58  fof(f426,plain,(
% 1.70/0.58    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0)) )),
% 1.70/0.58    inference(resolution,[],[f324,f76])).
% 1.70/0.58  fof(f76,plain,(
% 1.70/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.70/0.58    inference(equality_resolution,[],[f61])).
% 1.70/0.58  fof(f61,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.70/0.58    inference(cnf_transformation,[],[f40])).
% 1.70/0.58  fof(f324,plain,(
% 1.70/0.58    ( ! [X2] : (r2_hidden(sK3(sK0,k2_tarski(sK1,sK1),X2),k2_tarski(sK1,sK1)) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.70/0.58    inference(forward_demodulation,[],[f309,f298])).
% 1.70/0.58  fof(f309,plain,(
% 1.70/0.58    ( ! [X2] : (r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.70/0.58    inference(backward_demodulation,[],[f165,f298])).
% 1.70/0.58  fof(f515,plain,(
% 1.70/0.58    r2_orders_2(sK0,sK1,sK2) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)),
% 1.70/0.58    inference(subsumption_resolution,[],[f511,f46])).
% 1.70/0.58  fof(f511,plain,(
% 1.70/0.58    r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)),
% 1.70/0.58    inference(resolution,[],[f490,f73])).
% 1.70/0.58  fof(f73,plain,(
% 1.70/0.58    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.70/0.58    inference(equality_resolution,[],[f72])).
% 1.70/0.58  fof(f72,plain,(
% 1.70/0.58    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.70/0.58    inference(equality_resolution,[],[f63])).
% 1.70/0.58  fof(f63,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.70/0.58    inference(cnf_transformation,[],[f40])).
% 1.70/0.58  fof(f490,plain,(
% 1.70/0.58    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK1,sK1)) | r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f489,f436])).
% 1.70/0.58  fof(f489,plain,(
% 1.70/0.58    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~r2_hidden(X0,k2_tarski(sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,sK2) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)) )),
% 1.70/0.58    inference(superposition,[],[f483,f437])).
% 1.70/0.58  fof(f437,plain,(
% 1.70/0.58    sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1)) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),sK2)),
% 1.70/0.58    inference(resolution,[],[f436,f315])).
% 1.70/0.58  fof(f315,plain,(
% 1.70/0.58    r2_orders_2(sK0,sK1,sK2) | sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1))),
% 1.70/0.58    inference(backward_demodulation,[],[f209,f298])).
% 1.70/0.58  fof(f209,plain,(
% 1.70/0.58    r2_orders_2(sK0,sK1,sK2) | sK2 = sK4(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.70/0.58    inference(resolution,[],[f150,f48])).
% 1.70/0.58  fof(f483,plain,(
% 1.70/0.58    ( ! [X2] : (r2_orders_2(sK0,X2,sK4(sK2,sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X2,k2_tarski(sK1,sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,sK2)) )),
% 1.70/0.58    inference(resolution,[],[f354,f302])).
% 1.70/0.58  fof(f358,plain,(
% 1.70/0.58    ~r2_orders_2(sK0,sK3(sK0,k2_tarski(sK1,sK1),sK2),sK2) | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 1.70/0.58    inference(forward_demodulation,[],[f318,f298])).
% 1.70/0.58  fof(f318,plain,(
% 1.70/0.58    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK2),sK2)),
% 1.70/0.58    inference(backward_demodulation,[],[f259,f298])).
% 1.70/0.58  fof(f259,plain,(
% 1.70/0.58    ~r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK2),sK2) | r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.70/0.58    inference(resolution,[],[f180,f47])).
% 1.70/0.58  fof(f180,plain,(
% 1.70/0.58    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),X2)) )),
% 1.70/0.58    inference(forward_demodulation,[],[f175,f113])).
% 1.70/0.58  fof(f175,plain,(
% 1.70/0.58    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X2),X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.70/0.58    inference(resolution,[],[f98,f107])).
% 1.70/0.58  fof(f98,plain,(
% 1.70/0.58    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK3(sK0,X7,X8),X8) | r2_hidden(X8,a_2_0_orders_2(sK0,X7))) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f97,f41])).
% 1.70/0.58  fof(f97,plain,(
% 1.70/0.58    ( ! [X8,X7] : (~r2_orders_2(sK0,sK3(sK0,X7,X8),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X8,a_2_0_orders_2(sK0,X7)) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f96,f42])).
% 1.70/0.58  fof(f96,plain,(
% 1.70/0.58    ( ! [X8,X7] : (~r2_orders_2(sK0,sK3(sK0,X7,X8),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X8,a_2_0_orders_2(sK0,X7)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f95,f43])).
% 1.70/0.58  fof(f95,plain,(
% 1.70/0.58    ( ! [X8,X7] : (~r2_orders_2(sK0,sK3(sK0,X7,X8),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X8,a_2_0_orders_2(sK0,X7)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(subsumption_resolution,[],[f80,f44])).
% 1.70/0.58  fof(f80,plain,(
% 1.70/0.58    ( ! [X8,X7] : (~r2_orders_2(sK0,sK3(sK0,X7,X8),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X8,a_2_0_orders_2(sK0,X7)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.58    inference(resolution,[],[f45,f69])).
% 1.70/0.58  fof(f69,plain,(
% 1.70/0.58    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | ~r2_orders_2(X1,sK3(X1,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.70/0.58    inference(equality_resolution,[],[f60])).
% 1.70/0.58  fof(f60,plain,(
% 1.70/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK3(X1,X2,X3),X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f35])).
% 1.70/0.58  fof(f303,plain,(
% 1.70/0.58    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.70/0.58    inference(backward_demodulation,[],[f49,f298])).
% 1.70/0.58  fof(f49,plain,(
% 1.70/0.58    ~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.70/0.58    inference(cnf_transformation,[],[f30])).
% 1.70/0.58  % SZS output end Proof for theBenchmark
% 1.70/0.58  % (18872)------------------------------
% 1.70/0.58  % (18872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (18872)Termination reason: Refutation
% 1.70/0.58  
% 1.70/0.58  % (18872)Memory used [KB]: 6652
% 1.70/0.58  % (18872)Time elapsed: 0.145 s
% 1.70/0.58  % (18872)------------------------------
% 1.70/0.58  % (18872)------------------------------
% 1.70/0.58  % (18855)Success in time 0.222 s
%------------------------------------------------------------------------------
