%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:42 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  201 (2367 expanded)
%              Number of clauses        :  117 ( 687 expanded)
%              Number of leaves         :   20 ( 484 expanded)
%              Depth                    :   28
%              Number of atoms          :  766 (12568 expanded)
%              Number of equality atoms :  248 (2803 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK6),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK6),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK6),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK6),X0) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),X1),u1_struct_0(sK5))
            | ~ v1_tex_2(k1_tex_2(sK5,X1),sK5) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),X1),u1_struct_0(sK5))
            | v1_tex_2(k1_tex_2(sK5,X1),sK5) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
      | ~ v1_tex_2(k1_tex_2(sK5,sK6),sK5) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
      | v1_tex_2(k1_tex_2(sK5,sK6),sK5) )
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f76,f78,f77])).

fof(f119,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f79])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f20,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f117,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f118,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f65,f66])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f124,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f86])).

fof(f125,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f124])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f121,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ v1_tex_2(k1_tex_2(sK5,sK6),sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f120,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | v1_tex_2(k1_tex_2(sK5,sK6),sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f96,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_19454,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_19460,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_19462,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19643,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19460,c_19462])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_340,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_421,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_23,c_341])).

cnf(c_19451,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_19737,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19643,c_19451])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_19455,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_subset_1(k6_domain_1(X1,X0),X1) = iProver_top
    | v1_zfmisc_1(X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_117,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_120,plain,
    ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_33,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_236,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tex_2(X0,X1)
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_21])).

cnf(c_237,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_37,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK5,sK6),sK5)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_342,plain,
    ( ~ v1_tex_2(k1_tex_2(sK5,sK6),sK5)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
    inference(prop_impl,[status(thm)],[c_37])).

cnf(c_706,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK5,sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_342])).

cnf(c_707,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_709,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_40])).

cnf(c_710,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_709])).

cnf(c_25,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1653,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_1654,plain,
    ( m1_pre_topc(k1_tex_2(X0,sK6),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1653])).

cnf(c_1656,plain,
    ( m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_3576,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3589,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3576])).

cnf(c_4148,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
    inference(prop_impl,[status(thm)],[c_41,c_40,c_117,c_120,c_710,c_1656,c_3589])).

cnf(c_4149,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_4148])).

cnf(c_19445,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4149])).

cnf(c_19659,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19455,c_19445])).

cnf(c_42,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_43,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_101,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_103,plain,
    ( v2_struct_0(sK5) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_106,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_108,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_19808,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19659,c_42,c_43,c_44,c_103,c_108])).

cnf(c_19809,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_19808])).

cnf(c_19841,plain,
    ( u1_struct_0(k1_tex_2(sK5,sK6)) = u1_struct_0(sK5)
    | m1_pre_topc(k1_tex_2(sK5,sK6),sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19737,c_19809])).

cnf(c_1655,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | m1_pre_topc(k1_tex_2(X0,sK6),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_1657,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | m1_pre_topc(k1_tex_2(sK5,sK6),sK5) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_19865,plain,
    ( u1_struct_0(k1_tex_2(sK5,sK6)) = u1_struct_0(sK5)
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19841,c_42,c_43,c_117,c_120,c_1657,c_3589])).

cnf(c_32,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_243,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_21])).

cnf(c_244,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_38,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK5,sK6),sK5)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_344,plain,
    ( v1_tex_2(k1_tex_2(sK5,sK6),sK5)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
    inference(prop_impl,[status(thm)],[c_38])).

cnf(c_723,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK5,sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_344])).

cnf(c_724,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_726,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_40])).

cnf(c_727,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_726])).

cnf(c_4150,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
    inference(prop_impl,[status(thm)],[c_41,c_40,c_117,c_120,c_727,c_1656,c_3589])).

cnf(c_4151,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_4150])).

cnf(c_19446,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4151])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_19456,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_subset_1(k6_domain_1(X1,X0),X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19748,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19446,c_19456])).

cnf(c_19872,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19748,c_42,c_43,c_44,c_103,c_108])).

cnf(c_19873,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19872])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_11,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_258,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_11])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_424,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_259,c_341])).

cnf(c_19450,plain,
    ( v1_subset_1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_19878,plain,
    ( r1_tarski(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK5,sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19873,c_19450])).

cnf(c_11533,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_11534,plain,
    ( m1_pre_topc(k1_tex_2(sK5,sK6),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11533])).

cnf(c_12593,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12594,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12593])).

cnf(c_19888,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK5,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19878,c_42,c_43,c_117,c_120,c_1657,c_3589,c_11534,c_12594])).

cnf(c_607,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_15,c_18])).

cnf(c_19448,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_19894,plain,
    ( v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19888,c_19448])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1776,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_39])).

cnf(c_1777,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k1_tex_2(X0,sK6))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1776])).

cnf(c_1778,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k1_tex_2(X0,sK6)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1777])).

cnf(c_1780,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | v2_struct_0(k1_tex_2(sK5,sK6)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_19618,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
    | l1_pre_topc(k1_tex_2(sK5,sK6))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_19619,plain,
    ( m1_pre_topc(k1_tex_2(sK5,sK6),sK5) != iProver_top
    | l1_pre_topc(k1_tex_2(sK5,sK6)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19618])).

cnf(c_19898,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19894,c_42,c_43,c_117,c_120,c_1657,c_1780,c_3589,c_19619])).

cnf(c_19903,plain,
    ( u1_struct_0(k1_tex_2(sK5,sK6)) = u1_struct_0(sK5) ),
    inference(superposition,[status(thm)],[c_19865,c_19898])).

cnf(c_19459,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19461,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19785,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_tex_2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19459,c_19461])).

cnf(c_19930,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
    | l1_pre_topc(k1_tex_2(k1_tex_2(sK5,sK6),X0)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19903,c_19785])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1758,plain,
    ( v7_struct_0(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_1759,plain,
    ( v7_struct_0(k1_tex_2(X0,sK6))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1758])).

cnf(c_1760,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | v7_struct_0(k1_tex_2(X0,sK6)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1762,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | v7_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_19447,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1)) != iProver_top
    | v7_struct_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_19723,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v7_struct_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X1)) = iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19455,c_19447])).

cnf(c_20168,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v7_struct_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19723,c_19448])).

cnf(c_20173,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v7_struct_0(k1_tex_2(sK5,sK6)) != iProver_top
    | v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK5,sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19903,c_20168])).

cnf(c_20179,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v7_struct_0(k1_tex_2(sK5,sK6)) != iProver_top
    | v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20173,c_19903])).

cnf(c_20216,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19930,c_42,c_43,c_117,c_120,c_1657,c_1762,c_1780,c_3589,c_19619,c_19894,c_20179])).

cnf(c_20223,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_19454,c_20216])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:17:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.22/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.02  
% 3.22/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/1.02  
% 3.22/1.02  ------  iProver source info
% 3.22/1.02  
% 3.22/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.22/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/1.02  git: non_committed_changes: false
% 3.22/1.02  git: last_make_outside_of_git: false
% 3.22/1.02  
% 3.22/1.02  ------ 
% 3.22/1.02  ------ Parsing...
% 3.22/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  ------ Proving...
% 3.22/1.02  ------ Problem Properties 
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  clauses                                 38
% 3.22/1.02  conjectures                             6
% 3.22/1.02  EPR                                     9
% 3.22/1.02  Horn                                    27
% 3.22/1.02  unary                                   5
% 3.22/1.02  binary                                  12
% 3.22/1.02  lits                                    101
% 3.22/1.02  lits eq                                 10
% 3.22/1.02  fd_pure                                 0
% 3.22/1.02  fd_pseudo                               0
% 3.22/1.02  fd_cond                                 0
% 3.22/1.02  fd_pseudo_cond                          4
% 3.22/1.02  AC symbols                              0
% 3.22/1.02  
% 3.22/1.02  ------ Input Options Time Limit: Unbounded
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing...
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.22/1.02  Current options:
% 3.22/1.02  ------ 
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing...
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing...
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing...
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing...
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.22/1.02  
% 3.22/1.02  ------ Proving...
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  % SZS status Theorem for theBenchmark.p
% 3.22/1.02  
% 3.22/1.02   Resolution empty clause
% 3.22/1.02  
% 3.22/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/1.02  
% 3.22/1.02  fof(f22,conjecture,(
% 3.22/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f23,negated_conjecture,(
% 3.22/1.02    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.22/1.02    inference(negated_conjecture,[],[f22])).
% 3.22/1.02  
% 3.22/1.02  fof(f53,plain,(
% 3.22/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f23])).
% 3.22/1.02  
% 3.22/1.02  fof(f54,plain,(
% 3.22/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.22/1.02    inference(flattening,[],[f53])).
% 3.22/1.02  
% 3.22/1.02  fof(f75,plain,(
% 3.22/1.02    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.22/1.02    inference(nnf_transformation,[],[f54])).
% 3.22/1.02  
% 3.22/1.02  fof(f76,plain,(
% 3.22/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.22/1.02    inference(flattening,[],[f75])).
% 3.22/1.02  
% 3.22/1.02  fof(f78,plain,(
% 3.22/1.02    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK6),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK6),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK6),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK6),X0)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.22/1.02    introduced(choice_axiom,[])).
% 3.22/1.02  
% 3.22/1.02  fof(f77,plain,(
% 3.22/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK5),X1),u1_struct_0(sK5)) | ~v1_tex_2(k1_tex_2(sK5,X1),sK5)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK5),X1),u1_struct_0(sK5)) | v1_tex_2(k1_tex_2(sK5,X1),sK5)) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.22/1.02    introduced(choice_axiom,[])).
% 3.22/1.02  
% 3.22/1.02  fof(f79,plain,(
% 3.22/1.02    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) | ~v1_tex_2(k1_tex_2(sK5,sK6),sK5)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) | v1_tex_2(k1_tex_2(sK5,sK6),sK5)) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f76,f78,f77])).
% 3.22/1.02  
% 3.22/1.02  fof(f119,plain,(
% 3.22/1.02    m1_subset_1(sK6,u1_struct_0(sK5))),
% 3.22/1.02    inference(cnf_transformation,[],[f79])).
% 3.22/1.02  
% 3.22/1.02  fof(f12,axiom,(
% 3.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f36,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.22/1.02    inference(ennf_transformation,[],[f12])).
% 3.22/1.02  
% 3.22/1.02  fof(f101,plain,(
% 3.22/1.02    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f36])).
% 3.22/1.02  
% 3.22/1.02  fof(f5,axiom,(
% 3.22/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f68,plain,(
% 3.22/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.22/1.02    inference(nnf_transformation,[],[f5])).
% 3.22/1.02  
% 3.22/1.02  fof(f92,plain,(
% 3.22/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.22/1.02    inference(cnf_transformation,[],[f68])).
% 3.22/1.02  
% 3.22/1.02  fof(f14,axiom,(
% 3.22/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f39,plain,(
% 3.22/1.02    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f14])).
% 3.22/1.02  
% 3.22/1.02  fof(f71,plain,(
% 3.22/1.02    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/1.02    inference(nnf_transformation,[],[f39])).
% 3.22/1.02  
% 3.22/1.02  fof(f104,plain,(
% 3.22/1.02    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/1.02    inference(cnf_transformation,[],[f71])).
% 3.22/1.02  
% 3.22/1.02  fof(f93,plain,(
% 3.22/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f68])).
% 3.22/1.02  
% 3.22/1.02  fof(f20,axiom,(
% 3.22/1.02    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f49,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f20])).
% 3.22/1.02  
% 3.22/1.02  fof(f50,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.22/1.02    inference(flattening,[],[f49])).
% 3.22/1.02  
% 3.22/1.02  fof(f115,plain,(
% 3.22/1.02    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f50])).
% 3.22/1.02  
% 3.22/1.02  fof(f117,plain,(
% 3.22/1.02    ~v2_struct_0(sK5)),
% 3.22/1.02    inference(cnf_transformation,[],[f79])).
% 3.22/1.02  
% 3.22/1.02  fof(f118,plain,(
% 3.22/1.02    l1_pre_topc(sK5)),
% 3.22/1.02    inference(cnf_transformation,[],[f79])).
% 3.22/1.02  
% 3.22/1.02  fof(f3,axiom,(
% 3.22/1.02    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f63,plain,(
% 3.22/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.22/1.02    inference(nnf_transformation,[],[f3])).
% 3.22/1.02  
% 3.22/1.02  fof(f64,plain,(
% 3.22/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.22/1.02    inference(flattening,[],[f63])).
% 3.22/1.02  
% 3.22/1.02  fof(f65,plain,(
% 3.22/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.22/1.02    inference(rectify,[],[f64])).
% 3.22/1.02  
% 3.22/1.02  fof(f66,plain,(
% 3.22/1.02    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.22/1.02    introduced(choice_axiom,[])).
% 3.22/1.02  
% 3.22/1.02  fof(f67,plain,(
% 3.22/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f65,f66])).
% 3.22/1.02  
% 3.22/1.02  fof(f85,plain,(
% 3.22/1.02    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.22/1.02    inference(cnf_transformation,[],[f67])).
% 3.22/1.02  
% 3.22/1.02  fof(f126,plain,(
% 3.22/1.02    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 3.22/1.02    inference(equality_resolution,[],[f85])).
% 3.22/1.02  
% 3.22/1.02  fof(f86,plain,(
% 3.22/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.22/1.02    inference(cnf_transformation,[],[f67])).
% 3.22/1.02  
% 3.22/1.02  fof(f124,plain,(
% 3.22/1.02    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 3.22/1.02    inference(equality_resolution,[],[f86])).
% 3.22/1.02  
% 3.22/1.02  fof(f125,plain,(
% 3.22/1.02    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 3.22/1.02    inference(equality_resolution,[],[f124])).
% 3.22/1.02  
% 3.22/1.02  fof(f18,axiom,(
% 3.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f45,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.22/1.02    inference(ennf_transformation,[],[f18])).
% 3.22/1.02  
% 3.22/1.02  fof(f46,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.22/1.02    inference(flattening,[],[f45])).
% 3.22/1.02  
% 3.22/1.02  fof(f74,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.22/1.02    inference(nnf_transformation,[],[f46])).
% 3.22/1.02  
% 3.22/1.02  fof(f112,plain,(
% 3.22/1.02    ( ! [X2,X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f74])).
% 3.22/1.02  
% 3.22/1.02  fof(f129,plain,(
% 3.22/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(equality_resolution,[],[f112])).
% 3.22/1.02  
% 3.22/1.02  fof(f121,plain,(
% 3.22/1.02    ~v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) | ~v1_tex_2(k1_tex_2(sK5,sK6),sK5)),
% 3.22/1.02    inference(cnf_transformation,[],[f79])).
% 3.22/1.02  
% 3.22/1.02  fof(f15,axiom,(
% 3.22/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f24,plain,(
% 3.22/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.22/1.02    inference(pure_predicate_removal,[],[f15])).
% 3.22/1.02  
% 3.22/1.02  fof(f40,plain,(
% 3.22/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f24])).
% 3.22/1.02  
% 3.22/1.02  fof(f41,plain,(
% 3.22/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.22/1.02    inference(flattening,[],[f40])).
% 3.22/1.02  
% 3.22/1.02  fof(f106,plain,(
% 3.22/1.02    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f41])).
% 3.22/1.02  
% 3.22/1.02  fof(f10,axiom,(
% 3.22/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f33,plain,(
% 3.22/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f10])).
% 3.22/1.02  
% 3.22/1.02  fof(f34,plain,(
% 3.22/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.22/1.02    inference(flattening,[],[f33])).
% 3.22/1.02  
% 3.22/1.02  fof(f98,plain,(
% 3.22/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f34])).
% 3.22/1.02  
% 3.22/1.02  fof(f7,axiom,(
% 3.22/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f29,plain,(
% 3.22/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.22/1.02    inference(ennf_transformation,[],[f7])).
% 3.22/1.02  
% 3.22/1.02  fof(f95,plain,(
% 3.22/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f29])).
% 3.22/1.02  
% 3.22/1.02  fof(f113,plain,(
% 3.22/1.02    ( ! [X2,X0,X1] : (v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f74])).
% 3.22/1.02  
% 3.22/1.02  fof(f128,plain,(
% 3.22/1.02    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(equality_resolution,[],[f113])).
% 3.22/1.02  
% 3.22/1.02  fof(f120,plain,(
% 3.22/1.02    v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) | v1_tex_2(k1_tex_2(sK5,sK6),sK5)),
% 3.22/1.02    inference(cnf_transformation,[],[f79])).
% 3.22/1.02  
% 3.22/1.02  fof(f19,axiom,(
% 3.22/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f47,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 3.22/1.02    inference(ennf_transformation,[],[f19])).
% 3.22/1.02  
% 3.22/1.02  fof(f48,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 3.22/1.02    inference(flattening,[],[f47])).
% 3.22/1.02  
% 3.22/1.02  fof(f114,plain,(
% 3.22/1.02    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f48])).
% 3.22/1.02  
% 3.22/1.02  fof(f13,axiom,(
% 3.22/1.02    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f37,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f13])).
% 3.22/1.02  
% 3.22/1.02  fof(f38,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.22/1.02    inference(flattening,[],[f37])).
% 3.22/1.02  
% 3.22/1.02  fof(f102,plain,(
% 3.22/1.02    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f38])).
% 3.22/1.02  
% 3.22/1.02  fof(f4,axiom,(
% 3.22/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f27,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.22/1.02    inference(ennf_transformation,[],[f4])).
% 3.22/1.02  
% 3.22/1.02  fof(f91,plain,(
% 3.22/1.02    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f27])).
% 3.22/1.02  
% 3.22/1.02  fof(f105,plain,(
% 3.22/1.02    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f41])).
% 3.22/1.02  
% 3.22/1.02  fof(f8,axiom,(
% 3.22/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f30,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.22/1.02    inference(ennf_transformation,[],[f8])).
% 3.22/1.02  
% 3.22/1.02  fof(f96,plain,(
% 3.22/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f30])).
% 3.22/1.02  
% 3.22/1.02  fof(f16,axiom,(
% 3.22/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f25,plain,(
% 3.22/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.22/1.02    inference(pure_predicate_removal,[],[f16])).
% 3.22/1.02  
% 3.22/1.02  fof(f42,plain,(
% 3.22/1.02    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f25])).
% 3.22/1.02  
% 3.22/1.02  fof(f43,plain,(
% 3.22/1.02    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.22/1.02    inference(flattening,[],[f42])).
% 3.22/1.02  
% 3.22/1.02  fof(f108,plain,(
% 3.22/1.02    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f43])).
% 3.22/1.02  
% 3.22/1.02  fof(f21,axiom,(
% 3.22/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.02  
% 3.22/1.02  fof(f51,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.22/1.02    inference(ennf_transformation,[],[f21])).
% 3.22/1.02  
% 3.22/1.02  fof(f52,plain,(
% 3.22/1.02    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.22/1.02    inference(flattening,[],[f51])).
% 3.22/1.02  
% 3.22/1.02  fof(f116,plain,(
% 3.22/1.02    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.22/1.02    inference(cnf_transformation,[],[f52])).
% 3.22/1.02  
% 3.22/1.02  cnf(c_39,negated_conjecture,
% 3.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.22/1.02      inference(cnf_transformation,[],[f119]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19454,plain,
% 3.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_21,plain,
% 3.22/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19460,plain,
% 3.22/1.02      ( m1_pre_topc(X0,X1) != iProver_top
% 3.22/1.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_13,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19462,plain,
% 3.22/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.22/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19643,plain,
% 3.22/1.02      ( m1_pre_topc(X0,X1) != iProver_top
% 3.22/1.02      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19460,c_19462]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_23,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_subset_1(X0,X1) | X0 = X1 ),
% 3.22/1.02      inference(cnf_transformation,[],[f104]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_12,plain,
% 3.22/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_340,plain,
% 3.22/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.22/1.02      inference(prop_impl,[status(thm)],[c_12]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_341,plain,
% 3.22/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_340]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_421,plain,
% 3.22/1.02      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 3.22/1.02      inference(bin_hyper_res,[status(thm)],[c_23,c_341]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19451,plain,
% 3.22/1.02      ( X0 = X1
% 3.22/1.02      | v1_subset_1(X0,X1) = iProver_top
% 3.22/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19737,plain,
% 3.22/1.02      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.22/1.02      | m1_pre_topc(X1,X0) != iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
% 3.22/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19643,c_19451]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_35,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,X1)
% 3.22/1.02      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 3.22/1.02      | v1_zfmisc_1(X1)
% 3.22/1.02      | v1_xboole_0(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f115]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19455,plain,
% 3.22/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.22/1.02      | v1_subset_1(k6_domain_1(X1,X0),X1) = iProver_top
% 3.22/1.02      | v1_zfmisc_1(X1) = iProver_top
% 3.22/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_41,negated_conjecture,
% 3.22/1.02      ( ~ v2_struct_0(sK5) ),
% 3.22/1.02      inference(cnf_transformation,[],[f117]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_40,negated_conjecture,
% 3.22/1.02      ( l1_pre_topc(sK5) ),
% 3.22/1.02      inference(cnf_transformation,[],[f118]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_10,plain,
% 3.22/1.02      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.22/1.02      inference(cnf_transformation,[],[f126]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_117,plain,
% 3.22/1.02      ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5)) | sK5 = sK5 ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_9,plain,
% 3.22/1.02      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 3.22/1.02      inference(cnf_transformation,[],[f125]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_120,plain,
% 3.22/1.02      ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_33,plain,
% 3.22/1.02      ( v1_tex_2(X0,X1)
% 3.22/1.02      | ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f129]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_236,plain,
% 3.22/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | v1_tex_2(X0,X1)
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(global_propositional_subsumption,[status(thm)],[c_33,c_21]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_237,plain,
% 3.22/1.02      ( v1_tex_2(X0,X1)
% 3.22/1.02      | ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_236]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_37,negated_conjecture,
% 3.22/1.02      ( ~ v1_tex_2(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(cnf_transformation,[],[f121]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_342,plain,
% 3.22/1.02      ( ~ v1_tex_2(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(prop_impl,[status(thm)],[c_37]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_706,plain,
% 3.22/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1)
% 3.22/1.02      | k1_tex_2(sK5,sK6) != X0
% 3.22/1.02      | sK5 != X1 ),
% 3.22/1.02      inference(resolution_lifted,[status(thm)],[c_237,c_342]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_707,plain,
% 3.22/1.02      ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
% 3.22/1.02      | ~ l1_pre_topc(sK5) ),
% 3.22/1.02      inference(unflattening,[status(thm)],[c_706]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_709,plain,
% 3.22/1.02      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5) ),
% 3.22/1.02      inference(global_propositional_subsumption,[status(thm)],[c_707,c_40]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_710,plain,
% 3.22/1.02      ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_709]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_25,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/1.02      | v2_struct_0(X0)
% 3.22/1.02      | ~ l1_pre_topc(X0) ),
% 3.22/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1653,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.22/1.02      | v2_struct_0(X0)
% 3.22/1.02      | ~ l1_pre_topc(X0)
% 3.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.22/1.02      | sK6 != X1 ),
% 3.22/1.02      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1654,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(X0,sK6),X0)
% 3.22/1.02      | v2_struct_0(X0)
% 3.22/1.02      | ~ l1_pre_topc(X0)
% 3.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 3.22/1.02      inference(unflattening,[status(thm)],[c_1653]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1656,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | v2_struct_0(sK5)
% 3.22/1.02      | ~ l1_pre_topc(sK5)
% 3.22/1.02      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_1654]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_3576,plain,
% 3.22/1.02      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.22/1.02      theory(equality) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_3589,plain,
% 3.22/1.02      ( u1_struct_0(sK5) = u1_struct_0(sK5) | sK5 != sK5 ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_3576]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_4148,plain,
% 3.22/1.02      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(prop_impl,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_41,c_40,c_117,c_120,c_710,c_1656,c_3589]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_4149,plain,
% 3.22/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_4148]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19445,plain,
% 3.22/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_4149]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19659,plain,
% 3.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19455,c_19445]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_42,plain,
% 3.22/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_43,plain,
% 3.22/1.02      ( l1_pre_topc(sK5) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_44,plain,
% 3.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_18,plain,
% 3.22/1.02      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.22/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_101,plain,
% 3.22/1.02      ( v2_struct_0(X0) = iProver_top
% 3.22/1.02      | l1_struct_0(X0) != iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_103,plain,
% 3.22/1.02      ( v2_struct_0(sK5) = iProver_top
% 3.22/1.02      | l1_struct_0(sK5) != iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_101]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_15,plain,
% 3.22/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.22/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_106,plain,
% 3.22/1.02      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_108,plain,
% 3.22/1.02      ( l1_pre_topc(sK5) != iProver_top | l1_struct_0(sK5) = iProver_top ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_106]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19808,plain,
% 3.22/1.02      ( v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(global_propositional_subsumption,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_19659,c_42,c_43,c_44,c_103,c_108]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19809,plain,
% 3.22/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_19808]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19841,plain,
% 3.22/1.02      ( u1_struct_0(k1_tex_2(sK5,sK6)) = u1_struct_0(sK5)
% 3.22/1.02      | m1_pre_topc(k1_tex_2(sK5,sK6),sK5) != iProver_top
% 3.22/1.02      | l1_pre_topc(sK5) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19737,c_19809]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1655,plain,
% 3.22/1.02      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.22/1.02      | m1_pre_topc(k1_tex_2(X0,sK6),X0) = iProver_top
% 3.22/1.02      | v2_struct_0(X0) = iProver_top
% 3.22/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1657,plain,
% 3.22/1.02      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.22/1.02      | m1_pre_topc(k1_tex_2(sK5,sK6),sK5) = iProver_top
% 3.22/1.02      | v2_struct_0(sK5) = iProver_top
% 3.22/1.02      | l1_pre_topc(sK5) != iProver_top ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_1655]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19865,plain,
% 3.22/1.02      ( u1_struct_0(k1_tex_2(sK5,sK6)) = u1_struct_0(sK5)
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(global_propositional_subsumption,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_19841,c_42,c_43,c_117,c_120,c_1657,c_3589]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_32,plain,
% 3.22/1.02      ( ~ v1_tex_2(X0,X1)
% 3.22/1.02      | ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f128]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_243,plain,
% 3.22/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | ~ v1_tex_2(X0,X1)
% 3.22/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(global_propositional_subsumption,[status(thm)],[c_32,c_21]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_244,plain,
% 3.22/1.02      ( ~ v1_tex_2(X0,X1)
% 3.22/1.02      | ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_243]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_38,negated_conjecture,
% 3.22/1.02      ( v1_tex_2(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(cnf_transformation,[],[f120]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_344,plain,
% 3.22/1.02      ( v1_tex_2(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(prop_impl,[status(thm)],[c_38]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_723,plain,
% 3.22/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.22/1.02      | ~ l1_pre_topc(X1)
% 3.22/1.02      | k1_tex_2(sK5,sK6) != X0
% 3.22/1.02      | sK5 != X1 ),
% 3.22/1.02      inference(resolution_lifted,[status(thm)],[c_244,c_344]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_724,plain,
% 3.22/1.02      ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
% 3.22/1.02      | ~ l1_pre_topc(sK5) ),
% 3.22/1.02      inference(unflattening,[status(thm)],[c_723]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_726,plain,
% 3.22/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5) ),
% 3.22/1.02      inference(global_propositional_subsumption,[status(thm)],[c_724,c_40]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_727,plain,
% 3.22/1.02      ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_726]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_4150,plain,
% 3.22/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5))
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(prop_impl,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_41,c_40,c_117,c_120,c_727,c_1656,c_3589]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_4151,plain,
% 3.22/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_4150]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19446,plain,
% 3.22/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK5),sK6),u1_struct_0(sK5)) = iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_4151]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_34,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,X1)
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
% 3.22/1.02      | ~ v1_zfmisc_1(X1)
% 3.22/1.02      | v1_xboole_0(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f114]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19456,plain,
% 3.22/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.22/1.02      | v1_subset_1(k6_domain_1(X1,X0),X1) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(X1) != iProver_top
% 3.22/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19748,plain,
% 3.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19446,c_19456]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19872,plain,
% 3.22/1.02      ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(global_propositional_subsumption,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_19748,c_42,c_43,c_44,c_103,c_108]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19873,plain,
% 3.22/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_19872]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_22,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/1.02      | ~ v1_subset_1(X0,X1)
% 3.22/1.02      | ~ v1_zfmisc_1(X1)
% 3.22/1.02      | v1_xboole_0(X1)
% 3.22/1.02      | v1_xboole_0(X0) ),
% 3.22/1.02      inference(cnf_transformation,[],[f102]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_11,negated_conjecture,
% 3.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/1.02      | ~ v1_subset_1(X0,X1)
% 3.22/1.02      | ~ v1_xboole_0(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_258,plain,
% 3.22/1.02      ( ~ v1_zfmisc_1(X1)
% 3.22/1.02      | ~ v1_subset_1(X0,X1)
% 3.22/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/1.02      | v1_xboole_0(X0) ),
% 3.22/1.02      inference(global_propositional_subsumption,[status(thm)],[c_22,c_11]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_259,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/1.02      | ~ v1_subset_1(X0,X1)
% 3.22/1.02      | ~ v1_zfmisc_1(X1)
% 3.22/1.02      | v1_xboole_0(X0) ),
% 3.22/1.02      inference(renaming,[status(thm)],[c_258]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_424,plain,
% 3.22/1.02      ( ~ v1_subset_1(X0,X1)
% 3.22/1.02      | ~ r1_tarski(X0,X1)
% 3.22/1.02      | ~ v1_zfmisc_1(X1)
% 3.22/1.02      | v1_xboole_0(X0) ),
% 3.22/1.02      inference(bin_hyper_res,[status(thm)],[c_259,c_341]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19450,plain,
% 3.22/1.02      ( v1_subset_1(X0,X1) != iProver_top
% 3.22/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(X1) != iProver_top
% 3.22/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19878,plain,
% 3.22/1.02      ( r1_tarski(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK5,sK6))) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19873,c_19450]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_11533,plain,
% 3.22/1.02      ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.22/1.02      | ~ l1_pre_topc(sK5) ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_11534,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(sK5,sK6),sK5) != iProver_top
% 3.22/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.22/1.02      | l1_pre_topc(sK5) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_11533]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_12593,plain,
% 3.22/1.02      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.22/1.02      | r1_tarski(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_12594,plain,
% 3.22/1.02      ( m1_subset_1(u1_struct_0(k1_tex_2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.22/1.02      | r1_tarski(u1_struct_0(k1_tex_2(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_12593]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19888,plain,
% 3.22/1.02      ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK5,sK6))) = iProver_top ),
% 3.22/1.02      inference(global_propositional_subsumption,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_19878,c_42,c_43,c_117,c_120,c_1657,c_3589,c_11534,c_12594]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_607,plain,
% 3.22/1.02      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.22/1.02      inference(resolution,[status(thm)],[c_15,c_18]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19448,plain,
% 3.22/1.02      ( v2_struct_0(X0) = iProver_top
% 3.22/1.02      | l1_pre_topc(X0) != iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19894,plain,
% 3.22/1.02      ( v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19888,c_19448]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_26,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/1.02      | v2_struct_0(X1)
% 3.22/1.02      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f105]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1776,plain,
% 3.22/1.02      ( v2_struct_0(X0)
% 3.22/1.02      | ~ v2_struct_0(k1_tex_2(X0,X1))
% 3.22/1.02      | ~ l1_pre_topc(X0)
% 3.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.22/1.02      | sK6 != X1 ),
% 3.22/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_39]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1777,plain,
% 3.22/1.02      ( v2_struct_0(X0)
% 3.22/1.02      | ~ v2_struct_0(k1_tex_2(X0,sK6))
% 3.22/1.02      | ~ l1_pre_topc(X0)
% 3.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 3.22/1.02      inference(unflattening,[status(thm)],[c_1776]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1778,plain,
% 3.22/1.02      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.22/1.02      | v2_struct_0(X0) = iProver_top
% 3.22/1.02      | v2_struct_0(k1_tex_2(X0,sK6)) != iProver_top
% 3.22/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_1777]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1780,plain,
% 3.22/1.02      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.22/1.02      | v2_struct_0(k1_tex_2(sK5,sK6)) != iProver_top
% 3.22/1.02      | v2_struct_0(sK5) = iProver_top
% 3.22/1.02      | l1_pre_topc(sK5) != iProver_top ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_1778]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_16,plain,
% 3.22/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.22/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19618,plain,
% 3.22/1.02      ( ~ m1_pre_topc(k1_tex_2(sK5,sK6),sK5)
% 3.22/1.02      | l1_pre_topc(k1_tex_2(sK5,sK6))
% 3.22/1.02      | ~ l1_pre_topc(sK5) ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19619,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(sK5,sK6),sK5) != iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(sK5,sK6)) = iProver_top
% 3.22/1.02      | l1_pre_topc(sK5) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_19618]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19898,plain,
% 3.22/1.02      ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(global_propositional_subsumption,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_19894,c_42,c_43,c_117,c_120,c_1657,c_1780,c_3589,c_19619]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19903,plain,
% 3.22/1.02      ( u1_struct_0(k1_tex_2(sK5,sK6)) = u1_struct_0(sK5) ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19865,c_19898]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19459,plain,
% 3.22/1.02      ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
% 3.22/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.22/1.02      | v2_struct_0(X0) = iProver_top
% 3.22/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19461,plain,
% 3.22/1.02      ( m1_pre_topc(X0,X1) != iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top
% 3.22/1.02      | l1_pre_topc(X0) = iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19785,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.22/1.02      | v2_struct_0(X1) = iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(X1,X0)) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19459,c_19461]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19930,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(k1_tex_2(sK5,sK6),X0)) = iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19903,c_19785]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_27,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/1.02      | v7_struct_0(k1_tex_2(X1,X0))
% 3.22/1.02      | v2_struct_0(X1)
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1758,plain,
% 3.22/1.02      ( v7_struct_0(k1_tex_2(X0,X1))
% 3.22/1.02      | v2_struct_0(X0)
% 3.22/1.02      | ~ l1_pre_topc(X0)
% 3.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.22/1.02      | sK6 != X1 ),
% 3.22/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1759,plain,
% 3.22/1.02      ( v7_struct_0(k1_tex_2(X0,sK6))
% 3.22/1.02      | v2_struct_0(X0)
% 3.22/1.02      | ~ l1_pre_topc(X0)
% 3.22/1.02      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 3.22/1.02      inference(unflattening,[status(thm)],[c_1758]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1760,plain,
% 3.22/1.02      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.22/1.02      | v7_struct_0(k1_tex_2(X0,sK6)) = iProver_top
% 3.22/1.02      | v2_struct_0(X0) = iProver_top
% 3.22/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_1762,plain,
% 3.22/1.02      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.22/1.02      | v7_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
% 3.22/1.02      | v2_struct_0(sK5) = iProver_top
% 3.22/1.02      | l1_pre_topc(sK5) != iProver_top ),
% 3.22/1.02      inference(instantiation,[status(thm)],[c_1760]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_36,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 3.22/1.02      | ~ v7_struct_0(X1)
% 3.22/1.02      | v2_struct_0(X1)
% 3.22/1.02      | ~ l1_struct_0(X1) ),
% 3.22/1.02      inference(cnf_transformation,[],[f116]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_633,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 3.22/1.02      | ~ v7_struct_0(X1)
% 3.22/1.02      | v2_struct_0(X1)
% 3.22/1.02      | ~ l1_pre_topc(X2)
% 3.22/1.02      | X1 != X2 ),
% 3.22/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_634,plain,
% 3.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 3.22/1.02      | ~ v7_struct_0(X1)
% 3.22/1.02      | v2_struct_0(X1)
% 3.22/1.02      | ~ l1_pre_topc(X1) ),
% 3.22/1.02      inference(unflattening,[status(thm)],[c_633]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19447,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.22/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1)) != iProver_top
% 3.22/1.02      | v7_struct_0(X1) != iProver_top
% 3.22/1.02      | v2_struct_0(X1) = iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top ),
% 3.22/1.02      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_19723,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.22/1.02      | v7_struct_0(X1) != iProver_top
% 3.22/1.02      | v2_struct_0(X1) = iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(X1)) = iProver_top
% 3.22/1.02      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19455,c_19447]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_20168,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.22/1.02      | v7_struct_0(X1) != iProver_top
% 3.22/1.02      | v2_struct_0(X1) = iProver_top
% 3.22/1.02      | l1_pre_topc(X1) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(X1)) = iProver_top ),
% 3.22/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_19723,c_19448]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_20173,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v7_struct_0(k1_tex_2(sK5,sK6)) != iProver_top
% 3.22/1.02      | v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK5,sK6))) = iProver_top ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19903,c_20168]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_20179,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.22/1.02      | v7_struct_0(k1_tex_2(sK5,sK6)) != iProver_top
% 3.22/1.02      | v2_struct_0(k1_tex_2(sK5,sK6)) = iProver_top
% 3.22/1.02      | l1_pre_topc(k1_tex_2(sK5,sK6)) != iProver_top
% 3.22/1.02      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top ),
% 3.22/1.02      inference(light_normalisation,[status(thm)],[c_20173,c_19903]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_20216,plain,
% 3.22/1.02      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.22/1.02      inference(global_propositional_subsumption,
% 3.22/1.02                [status(thm)],
% 3.22/1.02                [c_19930,c_42,c_43,c_117,c_120,c_1657,c_1762,c_1780,c_3589,
% 3.22/1.02                 c_19619,c_19894,c_20179]) ).
% 3.22/1.02  
% 3.22/1.02  cnf(c_20223,plain,
% 3.22/1.02      ( $false ),
% 3.22/1.02      inference(superposition,[status(thm)],[c_19454,c_20216]) ).
% 3.22/1.02  
% 3.22/1.02  
% 3.22/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/1.02  
% 3.22/1.02  ------                               Statistics
% 3.22/1.02  
% 3.22/1.02  ------ Selected
% 3.22/1.02  
% 3.22/1.02  total_time:                             0.451
% 3.22/1.02  
%------------------------------------------------------------------------------
