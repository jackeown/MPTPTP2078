%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:25 EST 2020

% Result     : Theorem 23.31s
% Output     : CNFRefutation 23.31s
% Verified   : 
% Statistics : Number of formulae       :  256 (4188 expanded)
%              Number of clauses        :  161 (1339 expanded)
%              Number of leaves         :   27 ( 953 expanded)
%              Depth                    :   28
%              Number of atoms          :  912 (15566 expanded)
%              Number of equality atoms :  430 (2685 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),sK5),X0)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK4),X1),sK4)
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f64,f63])).

fof(f98,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f65])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f97,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f60])).

fof(f92,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f71,f70])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f109,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X0)
      | u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f70])).

fof(f99,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f107,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f102])).

fof(f108,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f107])).

fof(f96,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_470,plain,
    ( X0 != X1
    | X2 != X3
    | k6_domain_1(X0,X2) = k6_domain_1(X1,X3) ),
    theory(equality)).

cnf(c_12848,plain,
    ( X0 != k2_tarski(sK5,sK5)
    | X1 != sK5
    | k6_domain_1(X0,X1) = k6_domain_1(k2_tarski(sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_59106,plain,
    ( X0 != k2_tarski(sK5,sK5)
    | k6_domain_1(X0,sK5) = k6_domain_1(k2_tarski(sK5,sK5),sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_12848])).

cnf(c_75183,plain,
    ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) = k6_domain_1(k2_tarski(sK5,sK5),sK5)
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_59106])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1012,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1031,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2476,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_1031])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_33,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_35,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_84,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_86,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_88,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_90,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1340,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_2706,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2476,c_33,c_35,c_36,c_86,c_90,c_1340])).

cnf(c_5,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1033,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1011,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1024,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1025,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1016,plain,
    ( u1_struct_0(sK3(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3691,plain,
    ( u1_struct_0(sK3(X0,u1_struct_0(X1))) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1016])).

cnf(c_15196,plain,
    ( u1_struct_0(sK3(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_3691])).

cnf(c_15488,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | u1_struct_0(sK3(X0,u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15196,c_84,c_88])).

cnf(c_15489,plain,
    ( u1_struct_0(sK3(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15488])).

cnf(c_15497,plain,
    ( u1_struct_0(sK3(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_15489])).

cnf(c_76,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_79,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_85,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_89,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | u1_struct_0(sK3(X1,u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1393,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(sK3(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_15528,plain,
    ( u1_struct_0(sK3(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15497,c_32,c_30,c_76,c_79,c_85,c_89,c_1393])).

cnf(c_15537,plain,
    ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15528,c_1016])).

cnf(c_75,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_77,plain,
    ( m1_pre_topc(sK4,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3131,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1,u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1014])).

cnf(c_3169,plain,
    ( m1_pre_topc(sK4,sK4) != iProver_top
    | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3131])).

cnf(c_24,plain,
    ( m1_pre_topc(sK3(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4011,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(sK3(X1,X0))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_24,c_10])).

cnf(c_5343,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(sK3(X1,u1_struct_0(X0)))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4011,c_13])).

cnf(c_5344,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3(X1,u1_struct_0(X0))) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5343])).

cnf(c_5346,plain,
    ( m1_pre_topc(sK4,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5344])).

cnf(c_18107,plain,
    ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15537,c_33,c_35,c_77,c_86,c_90,c_3169,c_5346])).

cnf(c_18116,plain,
    ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))) = k2_tarski(X0,X0)
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_18107])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_101,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_21188,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))) = k2_tarski(X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18116,c_101])).

cnf(c_21189,plain,
    ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))) = k2_tarski(X0,X0)
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21188])).

cnf(c_21197,plain,
    ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_2706,c_21189])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1037,plain,
    ( sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1035,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3107,plain,
    ( sK0(X0,k2_tarski(X1,X1)) = X0
    | sK0(X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X1,X1) = k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_1037,c_1035])).

cnf(c_1015,plain,
    ( m1_pre_topc(sK3(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4981,plain,
    ( m1_pre_topc(sK3(X0,k2_tarski(X1,X1)),X0) = iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k2_tarski(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_1015])).

cnf(c_1034,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_47971,plain,
    ( m1_pre_topc(sK3(X0,k2_tarski(X1,X1)),X0) = iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4981,c_1034])).

cnf(c_15545,plain,
    ( m1_pre_topc(X0,sK3(sK4,u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15528,c_1025])).

cnf(c_16098,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_pre_topc(X0,sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15545,c_33,c_35,c_77,c_86,c_90,c_5346])).

cnf(c_16099,plain,
    ( m1_pre_topc(X0,sK3(sK4,u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_16098])).

cnf(c_47992,plain,
    ( m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3(sK4,u1_struct_0(sK4)))) != iProver_top
    | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_47971,c_16099])).

cnf(c_48106,plain,
    ( m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47992,c_15528])).

cnf(c_50617,plain,
    ( m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48106,c_33,c_35,c_77,c_86,c_90,c_3169,c_5346])).

cnf(c_50630,plain,
    ( sK0(X0,k2_tarski(X1,X1)) = X1
    | sK0(X0,k2_tarski(X1,X1)) = X0
    | m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X1,X1))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3107,c_50617])).

cnf(c_56811,plain,
    ( sK0(sK5,k2_tarski(X0,X0)) = X0
    | sK0(sK5,k2_tarski(X0,X0)) = sK5
    | m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2706,c_50630])).

cnf(c_58453,plain,
    ( sK0(sK5,k2_tarski(sK5,sK5)) = sK5
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21197,c_56811])).

cnf(c_1492,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1494,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_59275,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58453,c_33,c_35,c_36,c_86,c_90,c_1340,c_1494])).

cnf(c_59284,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_59275,c_1015])).

cnf(c_1691,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4)
    | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1692,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1691])).

cnf(c_2248,plain,
    ( ~ v1_xboole_0(k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2249,plain,
    ( v1_xboole_0(k2_tarski(sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_60596,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59284,c_33,c_35,c_36,c_86,c_90,c_1340,c_1494,c_1692,c_2249])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X0)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1023,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v7_struct_0(X0) != iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_60605,plain,
    ( v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_60596,c_1023])).

cnf(c_3690,plain,
    ( u1_struct_0(sK3(X0,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k2_tarski(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_1016])).

cnf(c_20844,plain,
    ( u1_struct_0(sK3(X0,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3690,c_1034])).

cnf(c_20849,plain,
    ( u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2706,c_20844])).

cnf(c_1694,plain,
    ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(k2_tarski(sK5,sK5))
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22088,plain,
    ( u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20849,c_32,c_30,c_29,c_85,c_89,c_1339,c_1492,c_1694,c_2248])).

cnf(c_22096,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22088,c_3131])).

cnf(c_22233,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22096,c_22088])).

cnf(c_37799,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22233,c_2249])).

cnf(c_37800,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_37799])).

cnf(c_60609,plain,
    ( v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_60596,c_37800])).

cnf(c_60655,plain,
    ( v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_60605,c_60609])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1030,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_60606,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_60596,c_1030])).

cnf(c_460,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1485,plain,
    ( X0 != X1
    | k6_domain_1(X0,X2) != X1
    | k6_domain_1(X0,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1583,plain,
    ( X0 != k6_domain_1(X1,X2)
    | k6_domain_1(X0,X3) = X0
    | k6_domain_1(X0,X3) != k6_domain_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_12824,plain,
    ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),X0) != k6_domain_1(k2_tarski(sK5,sK5),sK5)
    | k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),X0) = u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k6_domain_1(k2_tarski(sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_54896,plain,
    ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) != k6_domain_1(k2_tarski(sK5,sK5),sK5)
    | k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) = u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k6_domain_1(k2_tarski(sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_12824])).

cnf(c_4982,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK3(X1,u1_struct_0(X0)),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1015])).

cnf(c_1028,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_21415,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3(X1,u1_struct_0(X0))) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4982,c_1028])).

cnf(c_1029,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23699,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_struct_0(sK3(X1,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21415,c_1029])).

cnf(c_26128,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(sK3(X0,k2_tarski(sK5,sK5))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22088,c_23699])).

cnf(c_26200,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(sK3(X0,k2_tarski(sK5,sK5))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26128,c_22088])).

cnf(c_26229,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_26200])).

cnf(c_22319,plain,
    ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22233])).

cnf(c_26,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_280,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_13])).

cnf(c_281,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_1008,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_22104,plain,
    ( v2_tex_2(k2_tarski(sK5,sK5),X0) = iProver_top
    | m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
    | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22088,c_1008])).

cnf(c_22300,plain,
    ( v2_tex_2(k2_tarski(sK5,sK5),sK4) = iProver_top
    | m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
    | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
    | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22104])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_17419,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))))
    | v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
    | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
    | ~ l1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
    | k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) != u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_17420,plain,
    ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) != u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
    | m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) != iProver_top
    | v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
    | l1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17419])).

cnf(c_1857,plain,
    ( X0 != X1
    | u1_struct_0(X2) != X1
    | u1_struct_0(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_3328,plain,
    ( X0 != k2_tarski(sK5,sK5)
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = X0
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_6496,plain,
    ( k6_domain_1(k2_tarski(sK5,sK5),sK5) != k2_tarski(sK5,sK5)
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k6_domain_1(k2_tarski(sK5,sK5),sK5)
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_3328])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1548,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k2_tarski(X2,X2))
    | X0 != X2
    | X1 != k2_tarski(X2,X2) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_3026,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))))
    | ~ m1_subset_1(sK5,k2_tarski(sK5,sK5))
    | X0 != sK5
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_6216,plain,
    ( ~ m1_subset_1(sK5,k2_tarski(sK5,sK5))
    | m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))))
    | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_6217,plain,
    ( u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5)
    | sK5 != sK5
    | m1_subset_1(sK5,k2_tarski(sK5,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6216])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1026,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2515,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_1026])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2713,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2515,c_32,c_30,c_29,c_85,c_89,c_1378])).

cnf(c_28,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1013,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2716,plain,
    ( v2_tex_2(k2_tarski(sK5,sK5),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2713,c_1013])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1382,plain,
    ( m1_subset_1(X0,k2_tarski(X0,X0))
    | ~ r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2602,plain,
    ( m1_subset_1(sK5,k2_tarski(sK5,sK5))
    | ~ r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_2603,plain,
    ( m1_subset_1(sK5,k2_tarski(sK5,sK5)) = iProver_top
    | r2_hidden(sK5,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2602])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2598,plain,
    ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2599,plain,
    ( r2_hidden(sK5,k2_tarski(sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2598])).

cnf(c_1549,plain,
    ( ~ m1_subset_1(X0,k2_tarski(X0,X0))
    | v1_xboole_0(k2_tarski(X0,X0))
    | k6_domain_1(k2_tarski(X0,X0),X0) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2294,plain,
    ( ~ m1_subset_1(sK5,k2_tarski(sK5,sK5))
    | v1_xboole_0(k2_tarski(sK5,sK5))
    | k6_domain_1(k2_tarski(sK5,sK5),sK5) = k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_459,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1518,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_34,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75183,c_60655,c_60606,c_54896,c_26229,c_22319,c_22300,c_17420,c_6496,c_6217,c_2716,c_2603,c_2602,c_2599,c_2598,c_2294,c_2249,c_2248,c_1694,c_1692,c_1518,c_1494,c_1492,c_1340,c_1339,c_90,c_89,c_86,c_85,c_36,c_29,c_35,c_30,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.31/3.55  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.31/3.55  
% 23.31/3.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.31/3.55  
% 23.31/3.55  ------  iProver source info
% 23.31/3.55  
% 23.31/3.55  git: date: 2020-06-30 10:37:57 +0100
% 23.31/3.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.31/3.55  git: non_committed_changes: false
% 23.31/3.55  git: last_make_outside_of_git: false
% 23.31/3.55  
% 23.31/3.55  ------ 
% 23.31/3.55  ------ Parsing...
% 23.31/3.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.31/3.55  
% 23.31/3.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.31/3.55  
% 23.31/3.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.31/3.55  
% 23.31/3.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.31/3.55  ------ Proving...
% 23.31/3.55  ------ Problem Properties 
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  clauses                                 32
% 23.31/3.55  conjectures                             5
% 23.31/3.55  EPR                                     10
% 23.31/3.55  Horn                                    17
% 23.31/3.55  unary                                   7
% 23.31/3.55  binary                                  5
% 23.31/3.55  lits                                    99
% 23.31/3.55  lits eq                                 11
% 23.31/3.55  fd_pure                                 0
% 23.31/3.55  fd_pseudo                               0
% 23.31/3.55  fd_cond                                 0
% 23.31/3.55  fd_pseudo_cond                          2
% 23.31/3.55  AC symbols                              0
% 23.31/3.55  
% 23.31/3.55  ------ Input Options Time Limit: Unbounded
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  ------ 
% 23.31/3.55  Current options:
% 23.31/3.55  ------ 
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  ------ Proving...
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  % SZS status Theorem for theBenchmark.p
% 23.31/3.55  
% 23.31/3.55  % SZS output start CNFRefutation for theBenchmark.p
% 23.31/3.55  
% 23.31/3.55  fof(f19,conjecture,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f20,negated_conjecture,(
% 23.31/3.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 23.31/3.55    inference(negated_conjecture,[],[f19])).
% 23.31/3.55  
% 23.31/3.55  fof(f46,plain,(
% 23.31/3.55    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f20])).
% 23.31/3.55  
% 23.31/3.55  fof(f47,plain,(
% 23.31/3.55    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.31/3.55    inference(flattening,[],[f46])).
% 23.31/3.55  
% 23.31/3.55  fof(f64,plain,(
% 23.31/3.55    ( ! [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(X0),sK5),X0) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 23.31/3.55    introduced(choice_axiom,[])).
% 23.31/3.55  
% 23.31/3.55  fof(f63,plain,(
% 23.31/3.55    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK4),X1),sK4) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 23.31/3.55    introduced(choice_axiom,[])).
% 23.31/3.55  
% 23.31/3.55  fof(f65,plain,(
% 23.31/3.55    (~v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 23.31/3.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f64,f63])).
% 23.31/3.55  
% 23.31/3.55  fof(f98,plain,(
% 23.31/3.55    m1_subset_1(sK5,u1_struct_0(sK4))),
% 23.31/3.55    inference(cnf_transformation,[],[f65])).
% 23.31/3.55  
% 23.31/3.55  fof(f6,axiom,(
% 23.31/3.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f25,plain,(
% 23.31/3.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 23.31/3.55    inference(ennf_transformation,[],[f6])).
% 23.31/3.55  
% 23.31/3.55  fof(f26,plain,(
% 23.31/3.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 23.31/3.55    inference(flattening,[],[f25])).
% 23.31/3.55  
% 23.31/3.55  fof(f74,plain,(
% 23.31/3.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f26])).
% 23.31/3.55  
% 23.31/3.55  fof(f95,plain,(
% 23.31/3.55    ~v2_struct_0(sK4)),
% 23.31/3.55    inference(cnf_transformation,[],[f65])).
% 23.31/3.55  
% 23.31/3.55  fof(f97,plain,(
% 23.31/3.55    l1_pre_topc(sK4)),
% 23.31/3.55    inference(cnf_transformation,[],[f65])).
% 23.31/3.55  
% 23.31/3.55  fof(f10,axiom,(
% 23.31/3.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f31,plain,(
% 23.31/3.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f10])).
% 23.31/3.55  
% 23.31/3.55  fof(f32,plain,(
% 23.31/3.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(flattening,[],[f31])).
% 23.31/3.55  
% 23.31/3.55  fof(f78,plain,(
% 23.31/3.55    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f32])).
% 23.31/3.55  
% 23.31/3.55  fof(f8,axiom,(
% 23.31/3.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f29,plain,(
% 23.31/3.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.31/3.55    inference(ennf_transformation,[],[f8])).
% 23.31/3.55  
% 23.31/3.55  fof(f76,plain,(
% 23.31/3.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f29])).
% 23.31/3.55  
% 23.31/3.55  fof(f4,axiom,(
% 23.31/3.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f23,plain,(
% 23.31/3.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 23.31/3.55    inference(ennf_transformation,[],[f4])).
% 23.31/3.55  
% 23.31/3.55  fof(f72,plain,(
% 23.31/3.55    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f23])).
% 23.31/3.55  
% 23.31/3.55  fof(f2,axiom,(
% 23.31/3.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f70,plain,(
% 23.31/3.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f2])).
% 23.31/3.55  
% 23.31/3.55  fof(f105,plain,(
% 23.31/3.55    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 23.31/3.55    inference(definition_unfolding,[],[f72,f70])).
% 23.31/3.55  
% 23.31/3.55  fof(f13,axiom,(
% 23.31/3.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f36,plain,(
% 23.31/3.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 23.31/3.55    inference(ennf_transformation,[],[f13])).
% 23.31/3.55  
% 23.31/3.55  fof(f81,plain,(
% 23.31/3.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f36])).
% 23.31/3.55  
% 23.31/3.55  fof(f12,axiom,(
% 23.31/3.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f35,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.31/3.55    inference(ennf_transformation,[],[f12])).
% 23.31/3.55  
% 23.31/3.55  fof(f80,plain,(
% 23.31/3.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f35])).
% 23.31/3.55  
% 23.31/3.55  fof(f17,axiom,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f21,plain,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 23.31/3.55    inference(pure_predicate_removal,[],[f17])).
% 23.31/3.55  
% 23.31/3.55  fof(f42,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f21])).
% 23.31/3.55  
% 23.31/3.55  fof(f43,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(flattening,[],[f42])).
% 23.31/3.55  
% 23.31/3.55  fof(f60,plain,(
% 23.31/3.55    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))))),
% 23.31/3.55    introduced(choice_axiom,[])).
% 23.31/3.55  
% 23.31/3.55  fof(f61,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f60])).
% 23.31/3.55  
% 23.31/3.55  fof(f92,plain,(
% 23.31/3.55    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f61])).
% 23.31/3.55  
% 23.31/3.55  fof(f90,plain,(
% 23.31/3.55    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f61])).
% 23.31/3.55  
% 23.31/3.55  fof(f91,plain,(
% 23.31/3.55    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f61])).
% 23.31/3.55  
% 23.31/3.55  fof(f9,axiom,(
% 23.31/3.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f30,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.31/3.55    inference(ennf_transformation,[],[f9])).
% 23.31/3.55  
% 23.31/3.55  fof(f77,plain,(
% 23.31/3.55    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f30])).
% 23.31/3.55  
% 23.31/3.55  fof(f3,axiom,(
% 23.31/3.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f71,plain,(
% 23.31/3.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 23.31/3.55    inference(cnf_transformation,[],[f3])).
% 23.31/3.55  
% 23.31/3.55  fof(f104,plain,(
% 23.31/3.55    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 23.31/3.55    inference(definition_unfolding,[],[f71,f70])).
% 23.31/3.55  
% 23.31/3.55  fof(f1,axiom,(
% 23.31/3.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f48,plain,(
% 23.31/3.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 23.31/3.55    inference(nnf_transformation,[],[f1])).
% 23.31/3.55  
% 23.31/3.55  fof(f49,plain,(
% 23.31/3.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.31/3.55    inference(rectify,[],[f48])).
% 23.31/3.55  
% 23.31/3.55  fof(f50,plain,(
% 23.31/3.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 23.31/3.55    introduced(choice_axiom,[])).
% 23.31/3.55  
% 23.31/3.55  fof(f51,plain,(
% 23.31/3.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.31/3.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 23.31/3.55  
% 23.31/3.55  fof(f68,plain,(
% 23.31/3.55    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f51])).
% 23.31/3.55  
% 23.31/3.55  fof(f101,plain,(
% 23.31/3.55    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 23.31/3.55    inference(definition_unfolding,[],[f68,f70])).
% 23.31/3.55  
% 23.31/3.55  fof(f66,plain,(
% 23.31/3.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 23.31/3.55    inference(cnf_transformation,[],[f51])).
% 23.31/3.55  
% 23.31/3.55  fof(f103,plain,(
% 23.31/3.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 23.31/3.55    inference(definition_unfolding,[],[f66,f70])).
% 23.31/3.55  
% 23.31/3.55  fof(f109,plain,(
% 23.31/3.55    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 23.31/3.55    inference(equality_resolution,[],[f103])).
% 23.31/3.55  
% 23.31/3.55  fof(f14,axiom,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f22,plain,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 23.31/3.55    inference(pure_predicate_removal,[],[f14])).
% 23.31/3.55  
% 23.31/3.55  fof(f37,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f22])).
% 23.31/3.55  
% 23.31/3.55  fof(f38,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(flattening,[],[f37])).
% 23.31/3.55  
% 23.31/3.55  fof(f83,plain,(
% 23.31/3.55    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f38])).
% 23.31/3.55  
% 23.31/3.55  fof(f7,axiom,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f27,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f7])).
% 23.31/3.55  
% 23.31/3.55  fof(f28,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.31/3.55    inference(flattening,[],[f27])).
% 23.31/3.55  
% 23.31/3.55  fof(f75,plain,(
% 23.31/3.55    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f28])).
% 23.31/3.55  
% 23.31/3.55  fof(f18,axiom,(
% 23.31/3.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f44,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f18])).
% 23.31/3.55  
% 23.31/3.55  fof(f45,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(flattening,[],[f44])).
% 23.31/3.55  
% 23.31/3.55  fof(f62,plain,(
% 23.31/3.55    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(nnf_transformation,[],[f45])).
% 23.31/3.55  
% 23.31/3.55  fof(f94,plain,(
% 23.31/3.55    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f62])).
% 23.31/3.55  
% 23.31/3.55  fof(f110,plain,(
% 23.31/3.55    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(equality_resolution,[],[f94])).
% 23.31/3.55  
% 23.31/3.55  fof(f15,axiom,(
% 23.31/3.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f39,plain,(
% 23.31/3.55    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f15])).
% 23.31/3.55  
% 23.31/3.55  fof(f40,plain,(
% 23.31/3.55    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(flattening,[],[f39])).
% 23.31/3.55  
% 23.31/3.55  fof(f52,plain,(
% 23.31/3.55    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(nnf_transformation,[],[f40])).
% 23.31/3.55  
% 23.31/3.55  fof(f53,plain,(
% 23.31/3.55    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(rectify,[],[f52])).
% 23.31/3.55  
% 23.31/3.55  fof(f54,plain,(
% 23.31/3.55    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 23.31/3.55    introduced(choice_axiom,[])).
% 23.31/3.55  
% 23.31/3.55  fof(f55,plain,(
% 23.31/3.55    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.31/3.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 23.31/3.55  
% 23.31/3.55  fof(f86,plain,(
% 23.31/3.55    ( ! [X0,X1] : (v7_struct_0(X0) | u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f55])).
% 23.31/3.55  
% 23.31/3.55  fof(f11,axiom,(
% 23.31/3.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f33,plain,(
% 23.31/3.55    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 23.31/3.55    inference(ennf_transformation,[],[f11])).
% 23.31/3.55  
% 23.31/3.55  fof(f34,plain,(
% 23.31/3.55    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 23.31/3.55    inference(flattening,[],[f33])).
% 23.31/3.55  
% 23.31/3.55  fof(f79,plain,(
% 23.31/3.55    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f34])).
% 23.31/3.55  
% 23.31/3.55  fof(f106,plain,(
% 23.31/3.55    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.31/3.55    inference(definition_unfolding,[],[f79,f70])).
% 23.31/3.55  
% 23.31/3.55  fof(f99,plain,(
% 23.31/3.55    ~v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4)),
% 23.31/3.55    inference(cnf_transformation,[],[f65])).
% 23.31/3.55  
% 23.31/3.55  fof(f5,axiom,(
% 23.31/3.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 23.31/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.55  
% 23.31/3.55  fof(f24,plain,(
% 23.31/3.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 23.31/3.55    inference(ennf_transformation,[],[f5])).
% 23.31/3.55  
% 23.31/3.55  fof(f73,plain,(
% 23.31/3.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 23.31/3.55    inference(cnf_transformation,[],[f24])).
% 23.31/3.55  
% 23.31/3.55  fof(f67,plain,(
% 23.31/3.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 23.31/3.55    inference(cnf_transformation,[],[f51])).
% 23.31/3.55  
% 23.31/3.55  fof(f102,plain,(
% 23.31/3.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 23.31/3.55    inference(definition_unfolding,[],[f67,f70])).
% 23.31/3.55  
% 23.31/3.55  fof(f107,plain,(
% 23.31/3.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 23.31/3.55    inference(equality_resolution,[],[f102])).
% 23.31/3.55  
% 23.31/3.55  fof(f108,plain,(
% 23.31/3.55    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 23.31/3.55    inference(equality_resolution,[],[f107])).
% 23.31/3.55  
% 23.31/3.55  fof(f96,plain,(
% 23.31/3.55    v2_pre_topc(sK4)),
% 23.31/3.55    inference(cnf_transformation,[],[f65])).
% 23.31/3.55  
% 23.31/3.55  cnf(c_470,plain,
% 23.31/3.55      ( X0 != X1 | X2 != X3 | k6_domain_1(X0,X2) = k6_domain_1(X1,X3) ),
% 23.31/3.55      theory(equality) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_12848,plain,
% 23.31/3.55      ( X0 != k2_tarski(sK5,sK5)
% 23.31/3.55      | X1 != sK5
% 23.31/3.55      | k6_domain_1(X0,X1) = k6_domain_1(k2_tarski(sK5,sK5),sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_470]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_59106,plain,
% 23.31/3.55      ( X0 != k2_tarski(sK5,sK5)
% 23.31/3.55      | k6_domain_1(X0,sK5) = k6_domain_1(k2_tarski(sK5,sK5),sK5)
% 23.31/3.55      | sK5 != sK5 ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_12848]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_75183,plain,
% 23.31/3.55      ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) = k6_domain_1(k2_tarski(sK5,sK5),sK5)
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5)
% 23.31/3.55      | sK5 != sK5 ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_59106]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_29,negated_conjecture,
% 23.31/3.55      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 23.31/3.55      inference(cnf_transformation,[],[f98]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1012,plain,
% 23.31/3.55      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_7,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f74]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1031,plain,
% 23.31/3.55      ( m1_subset_1(X0,X1) != iProver_top
% 23.31/3.55      | r2_hidden(X0,X1) = iProver_top
% 23.31/3.55      | v1_xboole_0(X1) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2476,plain,
% 23.31/3.55      ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1012,c_1031]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_32,negated_conjecture,
% 23.31/3.55      ( ~ v2_struct_0(sK4) ),
% 23.31/3.55      inference(cnf_transformation,[],[f95]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_33,plain,
% 23.31/3.55      ( v2_struct_0(sK4) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_30,negated_conjecture,
% 23.31/3.55      ( l1_pre_topc(sK4) ),
% 23.31/3.55      inference(cnf_transformation,[],[f97]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_35,plain,
% 23.31/3.55      ( l1_pre_topc(sK4) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_36,plain,
% 23.31/3.55      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_11,plain,
% 23.31/3.55      ( v2_struct_0(X0)
% 23.31/3.55      | ~ l1_struct_0(X0)
% 23.31/3.55      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 23.31/3.55      inference(cnf_transformation,[],[f78]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_84,plain,
% 23.31/3.55      ( v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_struct_0(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_86,plain,
% 23.31/3.55      ( v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_struct_0(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_84]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_9,plain,
% 23.31/3.55      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f76]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_88,plain,
% 23.31/3.55      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_90,plain,
% 23.31/3.55      ( l1_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_88]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1339,plain,
% 23.31/3.55      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.31/3.55      | r2_hidden(sK5,u1_struct_0(sK4))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_7]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1340,plain,
% 23.31/3.55      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 23.31/3.55      | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_1339]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2706,plain,
% 23.31/3.55      ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_2476,c_33,c_35,c_36,c_86,c_90,c_1340]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5,plain,
% 23.31/3.55      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 23.31/3.55      | ~ r2_hidden(X0,X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f105]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1033,plain,
% 23.31/3.55      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 23.31/3.55      | r2_hidden(X0,X1) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1011,plain,
% 23.31/3.55      ( l1_pre_topc(sK4) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_14,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f81]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1024,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_13,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f80]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1025,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_23,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | v1_xboole_0(X0)
% 23.31/3.55      | u1_struct_0(sK3(X1,X0)) = X0 ),
% 23.31/3.55      inference(cnf_transformation,[],[f92]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1016,plain,
% 23.31/3.55      ( u1_struct_0(sK3(X0,X1)) = X1
% 23.31/3.55      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(X1) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3691,plain,
% 23.31/3.55      ( u1_struct_0(sK3(X0,u1_struct_0(X1))) = u1_struct_0(X1)
% 23.31/3.55      | m1_pre_topc(X1,X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1025,c_1016]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15196,plain,
% 23.31/3.55      ( u1_struct_0(sK3(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1024,c_3691]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15488,plain,
% 23.31/3.55      ( l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | u1_struct_0(sK3(X0,u1_struct_0(X0))) = u1_struct_0(X0) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_15196,c_84,c_88]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15489,plain,
% 23.31/3.55      ( u1_struct_0(sK3(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_15488]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15497,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1011,c_15489]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_76,plain,
% 23.31/3.55      ( m1_pre_topc(sK4,sK4) | ~ l1_pre_topc(sK4) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_14]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_79,plain,
% 23.31/3.55      ( ~ m1_pre_topc(sK4,sK4)
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.31/3.55      | ~ l1_pre_topc(sK4) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_13]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_85,plain,
% 23.31/3.55      ( v2_struct_0(sK4)
% 23.31/3.55      | ~ l1_struct_0(sK4)
% 23.31/3.55      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_11]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_89,plain,
% 23.31/3.55      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_9]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1391,plain,
% 23.31/3.55      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0))
% 23.31/3.55      | u1_struct_0(sK3(X1,u1_struct_0(X0))) = u1_struct_0(X0) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_23]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1393,plain,
% 23.31/3.55      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.31/3.55      | v2_struct_0(sK4)
% 23.31/3.55      | ~ l1_pre_topc(sK4)
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4))
% 23.31/3.55      | u1_struct_0(sK3(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1391]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15528,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK4,u1_struct_0(sK4))) = u1_struct_0(sK4) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_15497,c_32,c_30,c_76,c_79,c_85,c_89,c_1393]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15537,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),X0)) = X0
% 23.31/3.55      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | v1_xboole_0(X0) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_15528,c_1016]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_75,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_77,plain,
% 23.31/3.55      ( m1_pre_topc(sK4,sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_75]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ v2_struct_0(sK3(X1,X0))
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | v1_xboole_0(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f90]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1014,plain,
% 23.31/3.55      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(X1,X0)) != iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | v1_xboole_0(X0) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3131,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(X1,u1_struct_0(X0))) != iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1025,c_1014]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3169,plain,
% 23.31/3.55      ( m1_pre_topc(sK4,sK4) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_3131]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_24,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(X0,X1),X0)
% 23.31/3.55      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | v1_xboole_0(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f91]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_10,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f77]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4011,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | l1_pre_topc(sK3(X1,X0))
% 23.31/3.55      | v1_xboole_0(X0) ),
% 23.31/3.55      inference(resolution,[status(thm)],[c_24,c_10]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5343,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | l1_pre_topc(sK3(X1,u1_struct_0(X0)))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) ),
% 23.31/3.55      inference(resolution,[status(thm)],[c_4011,c_13]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5344,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(X1,u1_struct_0(X0))) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_5343]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5346,plain,
% 23.31/3.55      ( m1_pre_topc(sK4,sK4) != iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_5344]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18107,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),X0)) = X0
% 23.31/3.55      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | v1_xboole_0(X0) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_15537,c_33,c_35,c_77,c_86,c_90,c_3169,c_5346]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18116,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))) = k2_tarski(X0,X0)
% 23.31/3.55      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1033,c_18107]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4,plain,
% 23.31/3.55      ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
% 23.31/3.55      inference(cnf_transformation,[],[f104]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_101,plain,
% 23.31/3.55      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21188,plain,
% 23.31/3.55      ( r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 23.31/3.55      | u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))) = k2_tarski(X0,X0) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_18116,c_101]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21189,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))) = k2_tarski(X0,X0)
% 23.31/3.55      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_21188]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21197,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_2706,c_21189]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1,plain,
% 23.31/3.55      ( r2_hidden(sK0(X0,X1),X1)
% 23.31/3.55      | sK0(X0,X1) = X0
% 23.31/3.55      | k2_tarski(X0,X0) = X1 ),
% 23.31/3.55      inference(cnf_transformation,[],[f101]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1037,plain,
% 23.31/3.55      ( sK0(X0,X1) = X0
% 23.31/3.55      | k2_tarski(X0,X0) = X1
% 23.31/3.55      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3,plain,
% 23.31/3.55      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 23.31/3.55      inference(cnf_transformation,[],[f109]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1035,plain,
% 23.31/3.55      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3107,plain,
% 23.31/3.55      ( sK0(X0,k2_tarski(X1,X1)) = X0
% 23.31/3.55      | sK0(X0,k2_tarski(X1,X1)) = X1
% 23.31/3.55      | k2_tarski(X1,X1) = k2_tarski(X0,X0) ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1037,c_1035]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1015,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(X0,X1),X0) = iProver_top
% 23.31/3.55      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(X1) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4981,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(X0,k2_tarski(X1,X1)),X0) = iProver_top
% 23.31/3.55      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(X1,X1)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1033,c_1015]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1034,plain,
% 23.31/3.55      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_47971,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(X0,k2_tarski(X1,X1)),X0) = iProver_top
% 23.31/3.55      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(forward_subsumption_resolution,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_4981,c_1034]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15545,plain,
% 23.31/3.55      ( m1_pre_topc(X0,sK3(sK4,u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_15528,c_1025]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_16098,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | m1_pre_topc(X0,sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_15545,c_33,c_35,c_77,c_86,c_90,c_5346]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_16099,plain,
% 23.31/3.55      ( m1_pre_topc(X0,sK3(sK4,u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_16098]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_47992,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | r2_hidden(X0,u1_struct_0(sK3(sK4,u1_struct_0(sK4)))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_47971,c_16099]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_48106,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(sK4,u1_struct_0(sK4))) != iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_47992,c_15528]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_50617,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_48106,c_33,c_35,c_77,c_86,c_90,c_3169,c_5346]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_50630,plain,
% 23.31/3.55      ( sK0(X0,k2_tarski(X1,X1)) = X1
% 23.31/3.55      | sK0(X0,k2_tarski(X1,X1)) = X0
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X1,X1))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_3107,c_50617]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_56811,plain,
% 23.31/3.55      ( sK0(sK5,k2_tarski(X0,X0)) = X0
% 23.31/3.55      | sK0(sK5,k2_tarski(X0,X0)) = sK5
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK3(sK3(sK4,u1_struct_0(sK4)),k2_tarski(X0,X0))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_2706,c_50630]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_58453,plain,
% 23.31/3.55      ( sK0(sK5,k2_tarski(sK5,sK5)) = sK5
% 23.31/3.55      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_21197,c_56811]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1492,plain,
% 23.31/3.55      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.31/3.55      | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_5]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1494,plain,
% 23.31/3.55      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 23.31/3.55      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_59275,plain,
% 23.31/3.55      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_58453,c_33,c_35,c_36,c_86,c_90,c_1340,c_1494]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_59284,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_59275,c_1015]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1691,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4)
% 23.31/3.55      | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.31/3.55      | v2_struct_0(sK4)
% 23.31/3.55      | ~ l1_pre_topc(sK4)
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_24]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1692,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top
% 23.31/3.55      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_1691]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2248,plain,
% 23.31/3.55      ( ~ v1_xboole_0(k2_tarski(sK5,sK5)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_4]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2249,plain,
% 23.31/3.55      ( v1_xboole_0(k2_tarski(sK5,sK5)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_2248]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_60596,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_59284,c_33,c_35,c_36,c_86,c_90,c_1340,c_1494,c_1692,
% 23.31/3.55                 c_2249]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | ~ v7_struct_0(X0)
% 23.31/3.55      | v1_tdlat_3(X0)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | ~ v2_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f83]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1023,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | v7_struct_0(X0) != iProver_top
% 23.31/3.55      | v1_tdlat_3(X0) = iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | v2_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_60605,plain,
% 23.31/3.55      ( v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v2_pre_topc(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_60596,c_1023]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3690,plain,
% 23.31/3.55      ( u1_struct_0(sK3(X0,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
% 23.31/3.55      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(X1,X1)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1033,c_1016]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_20844,plain,
% 23.31/3.55      ( u1_struct_0(sK3(X0,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
% 23.31/3.55      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(forward_subsumption_resolution,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_3690,c_1034]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_20849,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5)
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_2706,c_20844]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1694,plain,
% 23.31/3.55      ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.31/3.55      | v2_struct_0(sK4)
% 23.31/3.55      | ~ l1_pre_topc(sK4)
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5))
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_23]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22088,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_20849,c_32,c_30,c_29,c_85,c_89,c_1339,c_1492,c_1694,
% 23.31/3.55                 c_2248]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22096,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_22088,c_3131]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22233,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_22096,c_22088]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_37799,plain,
% 23.31/3.55      ( l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_22233,c_2249]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_37800,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(X0,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_37799]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_60609,plain,
% 23.31/3.55      ( v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_60596,c_37800]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_60655,plain,
% 23.31/3.55      ( v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v2_pre_topc(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 23.31/3.55      inference(forward_subsumption_resolution,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_60605,c_60609]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_8,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v2_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f75]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1030,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | v2_pre_topc(X1) != iProver_top
% 23.31/3.55      | v2_pre_topc(X0) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_60606,plain,
% 23.31/3.55      ( l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v2_pre_topc(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | v2_pre_topc(sK4) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_60596,c_1030]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_460,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1485,plain,
% 23.31/3.55      ( X0 != X1 | k6_domain_1(X0,X2) != X1 | k6_domain_1(X0,X2) = X0 ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_460]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1583,plain,
% 23.31/3.55      ( X0 != k6_domain_1(X1,X2)
% 23.31/3.55      | k6_domain_1(X0,X3) = X0
% 23.31/3.55      | k6_domain_1(X0,X3) != k6_domain_1(X1,X2) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1485]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_12824,plain,
% 23.31/3.55      ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),X0) != k6_domain_1(k2_tarski(sK5,sK5),sK5)
% 23.31/3.55      | k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),X0) = u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k6_domain_1(k2_tarski(sK5,sK5),sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1583]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_54896,plain,
% 23.31/3.55      ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) != k6_domain_1(k2_tarski(sK5,sK5),sK5)
% 23.31/3.55      | k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) = u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k6_domain_1(k2_tarski(sK5,sK5),sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_12824]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4982,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | m1_pre_topc(sK3(X1,u1_struct_0(X0)),X1) = iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1025,c_1015]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1028,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | l1_pre_topc(X0) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21415,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | l1_pre_topc(sK3(X1,u1_struct_0(X0))) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_4982,c_1028]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1029,plain,
% 23.31/3.55      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_23699,plain,
% 23.31/3.55      ( m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | l1_struct_0(sK3(X1,u1_struct_0(X0))) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_21415,c_1029]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_26128,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_struct_0(sK3(X0,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_22088,c_23699]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_26200,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_struct_0(sK3(X0,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_26128,c_22088]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_26229,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_26200]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22319,plain,
% 23.31/3.55      ( m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_22233]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_26,plain,
% 23.31/3.55      ( v2_tex_2(u1_struct_0(X0),X1)
% 23.31/3.55      | ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ v1_tdlat_3(X0)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f110]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_280,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | v2_tex_2(u1_struct_0(X0),X1)
% 23.31/3.55      | ~ v1_tdlat_3(X0)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_26,c_13]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_281,plain,
% 23.31/3.55      ( v2_tex_2(u1_struct_0(X0),X1)
% 23.31/3.55      | ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | ~ v1_tdlat_3(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_280]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1008,plain,
% 23.31/3.55      ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
% 23.31/3.55      | m1_pre_topc(X0,X1) != iProver_top
% 23.31/3.55      | v1_tdlat_3(X0) != iProver_top
% 23.31/3.55      | v2_struct_0(X1) = iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | l1_pre_topc(X1) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22104,plain,
% 23.31/3.55      ( v2_tex_2(k2_tarski(sK5,sK5),X0) = iProver_top
% 23.31/3.55      | m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),X0) != iProver_top
% 23.31/3.55      | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v2_struct_0(X0) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | l1_pre_topc(X0) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_22088,c_1008]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22300,plain,
% 23.31/3.55      ( v2_tex_2(k2_tarski(sK5,sK5),sK4) = iProver_top
% 23.31/3.55      | m1_pre_topc(sK3(sK4,k2_tarski(sK5,sK5)),sK4) != iProver_top
% 23.31/3.55      | v1_tdlat_3(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | v2_struct_0(sK4) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK4) != iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_22104]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.31/3.55      | v7_struct_0(X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_struct_0(X1)
% 23.31/3.55      | k6_domain_1(u1_struct_0(X1),X0) != u1_struct_0(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f86]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17419,plain,
% 23.31/3.55      ( ~ m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))))
% 23.31/3.55      | v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
% 23.31/3.55      | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
% 23.31/3.55      | ~ l1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
% 23.31/3.55      | k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) != u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_17]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17420,plain,
% 23.31/3.55      ( k6_domain_1(u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))),sK5) != u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))
% 23.31/3.55      | m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) != iProver_top
% 23.31/3.55      | v7_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | v2_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = iProver_top
% 23.31/3.55      | l1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_17419]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1857,plain,
% 23.31/3.55      ( X0 != X1 | u1_struct_0(X2) != X1 | u1_struct_0(X2) = X0 ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_460]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3328,plain,
% 23.31/3.55      ( X0 != k2_tarski(sK5,sK5)
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = X0
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1857]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_6496,plain,
% 23.31/3.55      ( k6_domain_1(k2_tarski(sK5,sK5),sK5) != k2_tarski(sK5,sK5)
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) = k6_domain_1(k2_tarski(sK5,sK5),sK5)
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_3328]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_464,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.31/3.55      theory(equality) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1548,plain,
% 23.31/3.55      ( m1_subset_1(X0,X1)
% 23.31/3.55      | ~ m1_subset_1(X2,k2_tarski(X2,X2))
% 23.31/3.55      | X0 != X2
% 23.31/3.55      | X1 != k2_tarski(X2,X2) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_464]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3026,plain,
% 23.31/3.55      ( m1_subset_1(X0,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))))
% 23.31/3.55      | ~ m1_subset_1(sK5,k2_tarski(sK5,sK5))
% 23.31/3.55      | X0 != sK5
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1548]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_6216,plain,
% 23.31/3.55      ( ~ m1_subset_1(sK5,k2_tarski(sK5,sK5))
% 23.31/3.55      | m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))))
% 23.31/3.55      | u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5)
% 23.31/3.55      | sK5 != sK5 ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_3026]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_6217,plain,
% 23.31/3.55      ( u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5)
% 23.31/3.55      | sK5 != sK5
% 23.31/3.55      | m1_subset_1(sK5,k2_tarski(sK5,sK5)) != iProver_top
% 23.31/3.55      | m1_subset_1(sK5,u1_struct_0(sK3(sK4,k2_tarski(sK5,sK5)))) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_6216]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_12,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,X1)
% 23.31/3.55      | v1_xboole_0(X1)
% 23.31/3.55      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f106]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1026,plain,
% 23.31/3.55      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 23.31/3.55      | m1_subset_1(X1,X0) != iProver_top
% 23.31/3.55      | v1_xboole_0(X0) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2515,plain,
% 23.31/3.55      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_1012,c_1026]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1378,plain,
% 23.31/3.55      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK4))
% 23.31/3.55      | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_12]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2713,plain,
% 23.31/3.55      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_2515,c_32,c_30,c_29,c_85,c_89,c_1378]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_28,negated_conjecture,
% 23.31/3.55      ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
% 23.31/3.55      inference(cnf_transformation,[],[f99]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1013,plain,
% 23.31/3.55      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2716,plain,
% 23.31/3.55      ( v2_tex_2(k2_tarski(sK5,sK5),sK4) != iProver_top ),
% 23.31/3.55      inference(demodulation,[status(thm)],[c_2713,c_1013]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_6,plain,
% 23.31/3.55      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f73]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1382,plain,
% 23.31/3.55      ( m1_subset_1(X0,k2_tarski(X0,X0))
% 23.31/3.55      | ~ r2_hidden(X0,k2_tarski(X0,X0)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_6]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2602,plain,
% 23.31/3.55      ( m1_subset_1(sK5,k2_tarski(sK5,sK5))
% 23.31/3.55      | ~ r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1382]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2603,plain,
% 23.31/3.55      ( m1_subset_1(sK5,k2_tarski(sK5,sK5)) = iProver_top
% 23.31/3.55      | r2_hidden(sK5,k2_tarski(sK5,sK5)) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_2602]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2,plain,
% 23.31/3.55      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 23.31/3.55      inference(cnf_transformation,[],[f108]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2598,plain,
% 23.31/3.55      ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_2]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2599,plain,
% 23.31/3.55      ( r2_hidden(sK5,k2_tarski(sK5,sK5)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_2598]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1549,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k2_tarski(X0,X0))
% 23.31/3.55      | v1_xboole_0(k2_tarski(X0,X0))
% 23.31/3.55      | k6_domain_1(k2_tarski(X0,X0),X0) = k2_tarski(X0,X0) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_12]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2294,plain,
% 23.31/3.55      ( ~ m1_subset_1(sK5,k2_tarski(sK5,sK5))
% 23.31/3.55      | v1_xboole_0(k2_tarski(sK5,sK5))
% 23.31/3.55      | k6_domain_1(k2_tarski(sK5,sK5),sK5) = k2_tarski(sK5,sK5) ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_1549]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_459,plain,( X0 = X0 ),theory(equality) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1518,plain,
% 23.31/3.55      ( sK5 = sK5 ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_459]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_31,negated_conjecture,
% 23.31/3.55      ( v2_pre_topc(sK4) ),
% 23.31/3.55      inference(cnf_transformation,[],[f96]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_34,plain,
% 23.31/3.55      ( v2_pre_topc(sK4) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(contradiction,plain,
% 23.31/3.55      ( $false ),
% 23.31/3.55      inference(minisat,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_75183,c_60655,c_60606,c_54896,c_26229,c_22319,c_22300,
% 23.31/3.55                 c_17420,c_6496,c_6217,c_2716,c_2603,c_2602,c_2599,
% 23.31/3.55                 c_2598,c_2294,c_2249,c_2248,c_1694,c_1692,c_1518,c_1494,
% 23.31/3.55                 c_1492,c_1340,c_1339,c_90,c_89,c_86,c_85,c_36,c_29,c_35,
% 23.31/3.55                 c_30,c_34,c_33,c_32]) ).
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  % SZS output end CNFRefutation for theBenchmark.p
% 23.31/3.55  
% 23.31/3.55  ------                               Statistics
% 23.31/3.55  
% 23.31/3.55  ------ Selected
% 23.31/3.55  
% 23.31/3.55  total_time:                             2.754
% 23.31/3.55  
%------------------------------------------------------------------------------
