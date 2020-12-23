%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:32 EST 2020

% Result     : Theorem 15.35s
% Output     : CNFRefutation 15.35s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 492 expanded)
%              Number of clauses        :   72 ( 141 expanded)
%              Number of leaves         :   19 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  443 (2474 expanded)
%              Number of equality atoms :  137 ( 470 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) != k6_domain_1(u1_struct_0(X0),sK5)
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) != k6_domain_1(u1_struct_0(sK3),X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f31,f47,f46,f45])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f54])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_768,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_758,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_763,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3250,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k6_domain_1(X1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_763])).

cnf(c_24625,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r1_tarski(k6_domain_1(X1,X0),X2) = iProver_top
    | r2_hidden(sK1(k6_domain_1(X1,X0),X2),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_3250])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_769,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_46680,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r1_tarski(k6_domain_1(X1,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_24625,c_769])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_751,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_757,plain,
    ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2903,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_757])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_54,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_57,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_254,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1556,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1716,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k2_tarski(sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_255,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1226,plain,
    ( X0 != X1
    | k6_domain_1(u1_struct_0(sK3),sK5) != X1
    | k6_domain_1(u1_struct_0(sK3),sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1555,plain,
    ( X0 != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_2357,plain,
    ( k2_tarski(sK5,sK5) != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_3756,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2903,c_27,c_25,c_22,c_54,c_57,c_1556,c_1716,c_2357])).

cnf(c_3760,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_758])).

cnf(c_28,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_53,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_55,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_56,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_58,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_5353,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3760,c_28,c_30,c_33,c_55,c_58])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_752,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_1])).

cnf(c_206,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_745,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_1234,plain,
    ( m1_subset_1(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_752,c_745])).

cnf(c_2905,plain,
    ( k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5)
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_757])).

cnf(c_34,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1011,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1012,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_4637,plain,
    ( k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_34,c_1012])).

cnf(c_5357,plain,
    ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5353,c_4637])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_749,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_753,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1923,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_753])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2519,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1923,c_28,c_29,c_30,c_32])).

cnf(c_2520,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2519])).

cnf(c_5368,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(sK4,sK5))) = k6_domain_1(sK4,sK5)
    | r1_tarski(k6_domain_1(sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5357,c_2520])).

cnf(c_20,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3759,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_3756,c_20])).

cnf(c_4640,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(sK4,sK5))) != k6_domain_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_4637,c_3759])).

cnf(c_5428,plain,
    ( r1_tarski(k6_domain_1(sK4,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5368,c_4640])).

cnf(c_46940,plain,
    ( m1_subset_1(sK5,sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_46680,c_5428])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46940,c_1234,c_1012,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.35/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.35/2.49  
% 15.35/2.49  ------  iProver source info
% 15.35/2.49  
% 15.35/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.35/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.35/2.49  git: non_committed_changes: false
% 15.35/2.49  git: last_make_outside_of_git: false
% 15.35/2.49  
% 15.35/2.49  ------ 
% 15.35/2.49  ------ Parsing...
% 15.35/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  ------ Proving...
% 15.35/2.49  ------ Problem Properties 
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  clauses                                 28
% 15.35/2.49  conjectures                             8
% 15.35/2.49  EPR                                     12
% 15.35/2.49  Horn                                    19
% 15.35/2.49  unary                                   8
% 15.35/2.49  binary                                  7
% 15.35/2.49  lits                                    75
% 15.35/2.49  lits eq                                 5
% 15.35/2.49  fd_pure                                 0
% 15.35/2.49  fd_pseudo                               0
% 15.35/2.49  fd_cond                                 0
% 15.35/2.49  fd_pseudo_cond                          0
% 15.35/2.49  AC symbols                              0
% 15.35/2.49  
% 15.35/2.49  ------ Input Options Time Limit: Unbounded
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ 
% 15.35/2.49  Current options:
% 15.35/2.49  ------ 
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  % SZS status Theorem for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  fof(f2,axiom,(
% 15.35/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f15,plain,(
% 15.35/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f2])).
% 15.35/2.49  
% 15.35/2.49  fof(f36,plain,(
% 15.35/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.35/2.49    inference(nnf_transformation,[],[f15])).
% 15.35/2.49  
% 15.35/2.49  fof(f37,plain,(
% 15.35/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.35/2.49    inference(rectify,[],[f36])).
% 15.35/2.49  
% 15.35/2.49  fof(f38,plain,(
% 15.35/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f39,plain,(
% 15.35/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.35/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 15.35/2.49  
% 15.35/2.49  fof(f52,plain,(
% 15.35/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f39])).
% 15.35/2.49  
% 15.35/2.49  fof(f10,axiom,(
% 15.35/2.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f24,plain,(
% 15.35/2.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f10])).
% 15.35/2.49  
% 15.35/2.49  fof(f25,plain,(
% 15.35/2.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 15.35/2.49    inference(flattening,[],[f24])).
% 15.35/2.49  
% 15.35/2.49  fof(f64,plain,(
% 15.35/2.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f25])).
% 15.35/2.49  
% 15.35/2.49  fof(f5,axiom,(
% 15.35/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f17,plain,(
% 15.35/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f5])).
% 15.35/2.49  
% 15.35/2.49  fof(f59,plain,(
% 15.35/2.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.35/2.49    inference(cnf_transformation,[],[f17])).
% 15.35/2.49  
% 15.35/2.49  fof(f53,plain,(
% 15.35/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f39])).
% 15.35/2.49  
% 15.35/2.49  fof(f13,conjecture,(
% 15.35/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2))))))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f14,negated_conjecture,(
% 15.35/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2))))))),
% 15.35/2.49    inference(negated_conjecture,[],[f13])).
% 15.35/2.49  
% 15.35/2.49  fof(f30,plain,(
% 15.35/2.49    ? [X0] : (? [X1] : ((? [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f14])).
% 15.35/2.49  
% 15.35/2.49  fof(f31,plain,(
% 15.35/2.49    ? [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.35/2.49    inference(flattening,[],[f30])).
% 15.35/2.49  
% 15.35/2.49  fof(f47,plain,(
% 15.35/2.49    ( ! [X0,X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) != k6_domain_1(u1_struct_0(X0),sK5) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f46,plain,(
% 15.35/2.49    ( ! [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f45,plain,(
% 15.35/2.49    ? [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) != k6_domain_1(u1_struct_0(X0),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) != k6_domain_1(u1_struct_0(sK3),X2) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f48,plain,(
% 15.35/2.49    ((k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 15.35/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f31,f47,f46,f45])).
% 15.35/2.49  
% 15.35/2.49  fof(f75,plain,(
% 15.35/2.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f11,axiom,(
% 15.35/2.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f26,plain,(
% 15.35/2.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f11])).
% 15.35/2.49  
% 15.35/2.49  fof(f27,plain,(
% 15.35/2.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 15.35/2.49    inference(flattening,[],[f26])).
% 15.35/2.49  
% 15.35/2.49  fof(f65,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f27])).
% 15.35/2.49  
% 15.35/2.49  fof(f3,axiom,(
% 15.35/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f54,plain,(
% 15.35/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f3])).
% 15.35/2.49  
% 15.35/2.49  fof(f78,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f65,f54])).
% 15.35/2.49  
% 15.35/2.49  fof(f70,plain,(
% 15.35/2.49    ~v2_struct_0(sK3)),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f72,plain,(
% 15.35/2.49    l1_pre_topc(sK3)),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f9,axiom,(
% 15.35/2.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f22,plain,(
% 15.35/2.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f9])).
% 15.35/2.49  
% 15.35/2.49  fof(f23,plain,(
% 15.35/2.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 15.35/2.49    inference(flattening,[],[f22])).
% 15.35/2.49  
% 15.35/2.49  fof(f63,plain,(
% 15.35/2.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f23])).
% 15.35/2.49  
% 15.35/2.49  fof(f8,axiom,(
% 15.35/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f21,plain,(
% 15.35/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.35/2.49    inference(ennf_transformation,[],[f8])).
% 15.35/2.49  
% 15.35/2.49  fof(f62,plain,(
% 15.35/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f21])).
% 15.35/2.49  
% 15.35/2.49  fof(f76,plain,(
% 15.35/2.49    r2_hidden(sK5,sK4)),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f4,axiom,(
% 15.35/2.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f16,plain,(
% 15.35/2.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f4])).
% 15.35/2.49  
% 15.35/2.49  fof(f40,plain,(
% 15.35/2.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 15.35/2.49    inference(nnf_transformation,[],[f16])).
% 15.35/2.49  
% 15.35/2.49  fof(f56,plain,(
% 15.35/2.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f40])).
% 15.35/2.49  
% 15.35/2.49  fof(f1,axiom,(
% 15.35/2.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f32,plain,(
% 15.35/2.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 15.35/2.49    inference(nnf_transformation,[],[f1])).
% 15.35/2.49  
% 15.35/2.49  fof(f33,plain,(
% 15.35/2.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.35/2.49    inference(rectify,[],[f32])).
% 15.35/2.49  
% 15.35/2.49  fof(f34,plain,(
% 15.35/2.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f35,plain,(
% 15.35/2.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.35/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 15.35/2.49  
% 15.35/2.49  fof(f49,plain,(
% 15.35/2.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f35])).
% 15.35/2.49  
% 15.35/2.49  fof(f73,plain,(
% 15.35/2.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f12,axiom,(
% 15.35/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 15.35/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f28,plain,(
% 15.35/2.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.35/2.49    inference(ennf_transformation,[],[f12])).
% 15.35/2.49  
% 15.35/2.49  fof(f29,plain,(
% 15.35/2.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.35/2.49    inference(flattening,[],[f28])).
% 15.35/2.49  
% 15.35/2.49  fof(f41,plain,(
% 15.35/2.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.35/2.49    inference(nnf_transformation,[],[f29])).
% 15.35/2.49  
% 15.35/2.49  fof(f42,plain,(
% 15.35/2.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.35/2.49    inference(rectify,[],[f41])).
% 15.35/2.49  
% 15.35/2.49  fof(f43,plain,(
% 15.35/2.49    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f44,plain,(
% 15.35/2.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.35/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 15.35/2.49  
% 15.35/2.49  fof(f66,plain,(
% 15.35/2.49    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f44])).
% 15.35/2.49  
% 15.35/2.49  fof(f71,plain,(
% 15.35/2.49    v2_pre_topc(sK3)),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f74,plain,(
% 15.35/2.49    v2_tex_2(sK4,sK3)),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  fof(f77,plain,(
% 15.35/2.49    k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)),
% 15.35/2.49    inference(cnf_transformation,[],[f48])).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3,plain,
% 15.35/2.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_768,plain,
% 15.35/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.35/2.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_14,plain,
% 15.35/2.49      ( ~ m1_subset_1(X0,X1)
% 15.35/2.49      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 15.35/2.49      | v1_xboole_0(X1) ),
% 15.35/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_758,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.35/2.49      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 15.35/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_9,plain,
% 15.35/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.35/2.49      | ~ r2_hidden(X2,X0)
% 15.35/2.49      | r2_hidden(X2,X1) ),
% 15.35/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_763,plain,
% 15.35/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.35/2.49      | r2_hidden(X2,X0) != iProver_top
% 15.35/2.49      | r2_hidden(X2,X1) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3250,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.35/2.49      | r2_hidden(X2,X1) = iProver_top
% 15.35/2.49      | r2_hidden(X2,k6_domain_1(X1,X0)) != iProver_top
% 15.35/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_758,c_763]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_24625,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.35/2.49      | r1_tarski(k6_domain_1(X1,X0),X2) = iProver_top
% 15.35/2.49      | r2_hidden(sK1(k6_domain_1(X1,X0),X2),X1) = iProver_top
% 15.35/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_768,c_3250]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2,plain,
% 15.35/2.49      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 15.35/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_769,plain,
% 15.35/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.35/2.49      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_46680,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.35/2.49      | r1_tarski(k6_domain_1(X1,X0),X1) = iProver_top
% 15.35/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_24625,c_769]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22,negated_conjecture,
% 15.35/2.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 15.35/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_751,plain,
% 15.35/2.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_15,plain,
% 15.35/2.49      ( ~ m1_subset_1(X0,X1)
% 15.35/2.49      | v1_xboole_0(X1)
% 15.35/2.49      | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f78]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_757,plain,
% 15.35/2.49      ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
% 15.35/2.49      | m1_subset_1(X0,X1) != iProver_top
% 15.35/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2903,plain,
% 15.35/2.49      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
% 15.35/2.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_751,c_757]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_27,negated_conjecture,
% 15.35/2.49      ( ~ v2_struct_0(sK3) ),
% 15.35/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_25,negated_conjecture,
% 15.35/2.49      ( l1_pre_topc(sK3) ),
% 15.35/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_13,plain,
% 15.35/2.49      ( v2_struct_0(X0)
% 15.35/2.49      | ~ l1_struct_0(X0)
% 15.35/2.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 15.35/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_54,plain,
% 15.35/2.49      ( v2_struct_0(sK3)
% 15.35/2.49      | ~ l1_struct_0(sK3)
% 15.35/2.49      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_13]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_12,plain,
% 15.35/2.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_57,plain,
% 15.35/2.49      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_254,plain,( X0 = X0 ),theory(equality) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1556,plain,
% 15.35/2.49      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_254]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1109,plain,
% 15.35/2.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.35/2.49      | v1_xboole_0(u1_struct_0(X1))
% 15.35/2.49      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_15]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1716,plain,
% 15.35/2.49      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 15.35/2.49      | v1_xboole_0(u1_struct_0(sK3))
% 15.35/2.49      | k2_tarski(sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1109]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_255,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1226,plain,
% 15.35/2.49      ( X0 != X1
% 15.35/2.49      | k6_domain_1(u1_struct_0(sK3),sK5) != X1
% 15.35/2.49      | k6_domain_1(u1_struct_0(sK3),sK5) = X0 ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_255]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1555,plain,
% 15.35/2.49      ( X0 != k6_domain_1(u1_struct_0(sK3),sK5)
% 15.35/2.49      | k6_domain_1(u1_struct_0(sK3),sK5) = X0
% 15.35/2.49      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1226]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2357,plain,
% 15.35/2.49      ( k2_tarski(sK5,sK5) != k6_domain_1(u1_struct_0(sK3),sK5)
% 15.35/2.49      | k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
% 15.35/2.49      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1555]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3756,plain,
% 15.35/2.49      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_2903,c_27,c_25,c_22,c_54,c_57,c_1556,c_1716,c_2357]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3760,plain,
% 15.35/2.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 15.35/2.49      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 15.35/2.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_3756,c_758]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_28,plain,
% 15.35/2.49      ( v2_struct_0(sK3) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_30,plain,
% 15.35/2.49      ( l1_pre_topc(sK3) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_33,plain,
% 15.35/2.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_53,plain,
% 15.35/2.49      ( v2_struct_0(X0) = iProver_top
% 15.35/2.49      | l1_struct_0(X0) != iProver_top
% 15.35/2.49      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_55,plain,
% 15.35/2.49      ( v2_struct_0(sK3) = iProver_top
% 15.35/2.49      | l1_struct_0(sK3) != iProver_top
% 15.35/2.49      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_53]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_56,plain,
% 15.35/2.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_58,plain,
% 15.35/2.49      ( l1_struct_0(sK3) = iProver_top
% 15.35/2.49      | l1_pre_topc(sK3) != iProver_top ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_56]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5353,plain,
% 15.35/2.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_3760,c_28,c_30,c_33,c_55,c_58]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_21,negated_conjecture,
% 15.35/2.49      ( r2_hidden(sK5,sK4) ),
% 15.35/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_752,plain,
% 15.35/2.49      ( r2_hidden(sK5,sK4) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_7,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.35/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.35/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_205,plain,
% 15.35/2.49      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 15.35/2.49      inference(global_propositional_subsumption,[status(thm)],[c_7,c_1]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_206,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_205]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_745,plain,
% 15.35/2.49      ( m1_subset_1(X0,X1) = iProver_top
% 15.35/2.49      | r2_hidden(X0,X1) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1234,plain,
% 15.35/2.49      ( m1_subset_1(sK5,sK4) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_752,c_745]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2905,plain,
% 15.35/2.49      ( k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5)
% 15.35/2.49      | v1_xboole_0(sK4) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_1234,c_757]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_34,plain,
% 15.35/2.49      ( r2_hidden(sK5,sK4) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1011,plain,
% 15.35/2.49      ( ~ r2_hidden(sK5,sK4) | ~ v1_xboole_0(sK4) ),
% 15.35/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1012,plain,
% 15.35/2.49      ( r2_hidden(sK5,sK4) != iProver_top
% 15.35/2.49      | v1_xboole_0(sK4) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4637,plain,
% 15.35/2.49      ( k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5) ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_2905,c_34,c_1012]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5357,plain,
% 15.35/2.49      ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.35/2.49      inference(light_normalisation,[status(thm)],[c_5353,c_4637]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_24,negated_conjecture,
% 15.35/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 15.35/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_749,plain,
% 15.35/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_19,plain,
% 15.35/2.49      ( ~ v2_tex_2(X0,X1)
% 15.35/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.35/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.35/2.49      | ~ r1_tarski(X2,X0)
% 15.35/2.49      | ~ v2_pre_topc(X1)
% 15.35/2.49      | v2_struct_0(X1)
% 15.35/2.49      | ~ l1_pre_topc(X1)
% 15.35/2.49      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 15.35/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_753,plain,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
% 15.35/2.49      | v2_tex_2(X1,X0) != iProver_top
% 15.35/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.35/2.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.35/2.49      | r1_tarski(X2,X1) != iProver_top
% 15.35/2.49      | v2_pre_topc(X0) != iProver_top
% 15.35/2.49      | v2_struct_0(X0) = iProver_top
% 15.35/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1923,plain,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 15.35/2.49      | v2_tex_2(sK4,sK3) != iProver_top
% 15.35/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.35/2.49      | r1_tarski(X0,sK4) != iProver_top
% 15.35/2.49      | v2_pre_topc(sK3) != iProver_top
% 15.35/2.49      | v2_struct_0(sK3) = iProver_top
% 15.35/2.49      | l1_pre_topc(sK3) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_749,c_753]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_26,negated_conjecture,
% 15.35/2.49      ( v2_pre_topc(sK3) ),
% 15.35/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_29,plain,
% 15.35/2.49      ( v2_pre_topc(sK3) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_23,negated_conjecture,
% 15.35/2.49      ( v2_tex_2(sK4,sK3) ),
% 15.35/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_32,plain,
% 15.35/2.49      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2519,plain,
% 15.35/2.49      ( r1_tarski(X0,sK4) != iProver_top
% 15.35/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.35/2.49      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_1923,c_28,c_29,c_30,c_32]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_2520,plain,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 15.35/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.35/2.49      | r1_tarski(X0,sK4) != iProver_top ),
% 15.35/2.49      inference(renaming,[status(thm)],[c_2519]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5368,plain,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(sK4,sK5))) = k6_domain_1(sK4,sK5)
% 15.35/2.49      | r1_tarski(k6_domain_1(sK4,sK5),sK4) != iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_5357,c_2520]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_20,negated_conjecture,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 15.35/2.49      inference(cnf_transformation,[],[f77]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_3759,plain,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_tarski(sK5,sK5))) != k2_tarski(sK5,sK5) ),
% 15.35/2.49      inference(demodulation,[status(thm)],[c_3756,c_20]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_4640,plain,
% 15.35/2.49      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(sK4,sK5))) != k6_domain_1(sK4,sK5) ),
% 15.35/2.49      inference(demodulation,[status(thm)],[c_4637,c_3759]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5428,plain,
% 15.35/2.49      ( r1_tarski(k6_domain_1(sK4,sK5),sK4) != iProver_top ),
% 15.35/2.49      inference(global_propositional_subsumption,
% 15.35/2.49                [status(thm)],
% 15.35/2.49                [c_5368,c_4640]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_46940,plain,
% 15.35/2.49      ( m1_subset_1(sK5,sK4) != iProver_top
% 15.35/2.49      | v1_xboole_0(sK4) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_46680,c_5428]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(contradiction,plain,
% 15.35/2.49      ( $false ),
% 15.35/2.49      inference(minisat,[status(thm)],[c_46940,c_1234,c_1012,c_34]) ).
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  ------                               Statistics
% 15.35/2.49  
% 15.35/2.49  ------ Selected
% 15.35/2.49  
% 15.35/2.49  total_time:                             1.614
% 15.35/2.49  
%------------------------------------------------------------------------------
