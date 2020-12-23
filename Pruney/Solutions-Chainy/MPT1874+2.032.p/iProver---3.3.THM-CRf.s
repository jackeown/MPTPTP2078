%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:33 EST 2020

% Result     : Theorem 7.17s
% Output     : CNFRefutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 261 expanded)
%              Number of clauses        :   64 (  74 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  439 (1400 expanded)
%              Number of equality atoms :   85 ( 226 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,conjecture,(
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
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)))
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f44,f43,f42])).

fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f11,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,sK4),X0)
    | r2_hidden(sK1(X0,sK4),X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_18810,plain,
    ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5))
    | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_6180])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1783,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5373,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),sK4)
    | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1784,plain,
    ( r1_tarski(X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5374,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),sK4)
    | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_1145,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2089,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | X0 != k6_domain_1(sK4,sK5)
    | X1 != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_2871,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | X0 != k6_domain_1(sK4,sK5)
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_4564,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | k2_tarski(sK5,sK5) != k6_domain_1(sK4,sK5)
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2871])).

cnf(c_1143,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1793,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(X1,sK4)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_2299,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_3989,plain,
    ( ~ r1_tarski(k2_tarski(sK5,sK5),sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_1139,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2872,plain,
    ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1513,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1515,plain,
    ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2446,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1513,c_1515])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_276,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_277,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_281,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_23,c_21])).

cnf(c_282,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_1661,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_2053,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_1733,plain,
    ( ~ m1_subset_1(X0,sK4)
    | v1_xboole_0(sK4)
    | k2_tarski(X0,X0) = k6_domain_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1994,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | v1_xboole_0(sK4)
    | k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1734,plain,
    ( ~ m1_subset_1(X0,sK4)
    | m1_subset_1(k6_domain_1(sK4,X0),k1_zfmisc_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1959,plain,
    ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_1698,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1932,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_1777,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_1140,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1701,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1776,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1673,plain,
    ( m1_subset_1(sK5,sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1670,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_52,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_54,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_53,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_49,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_51,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_50,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18810,c_5373,c_5374,c_4564,c_3989,c_2872,c_2446,c_2053,c_1994,c_1959,c_1932,c_1777,c_1776,c_1673,c_1670,c_54,c_53,c_51,c_50,c_16,c_17,c_18,c_19,c_20,c_26,c_21,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.17/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.17/1.52  
% 7.17/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.17/1.52  
% 7.17/1.52  ------  iProver source info
% 7.17/1.52  
% 7.17/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.17/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.17/1.52  git: non_committed_changes: false
% 7.17/1.52  git: last_make_outside_of_git: false
% 7.17/1.52  
% 7.17/1.52  ------ 
% 7.17/1.52  
% 7.17/1.52  ------ Input Options
% 7.17/1.52  
% 7.17/1.52  --out_options                           all
% 7.17/1.52  --tptp_safe_out                         true
% 7.17/1.52  --problem_path                          ""
% 7.17/1.52  --include_path                          ""
% 7.17/1.52  --clausifier                            res/vclausify_rel
% 7.17/1.52  --clausifier_options                    --mode clausify
% 7.17/1.52  --stdin                                 false
% 7.17/1.52  --stats_out                             all
% 7.17/1.52  
% 7.17/1.52  ------ General Options
% 7.17/1.52  
% 7.17/1.52  --fof                                   false
% 7.17/1.52  --time_out_real                         305.
% 7.17/1.52  --time_out_virtual                      -1.
% 7.17/1.52  --symbol_type_check                     false
% 7.17/1.52  --clausify_out                          false
% 7.17/1.52  --sig_cnt_out                           false
% 7.17/1.52  --trig_cnt_out                          false
% 7.17/1.52  --trig_cnt_out_tolerance                1.
% 7.17/1.52  --trig_cnt_out_sk_spl                   false
% 7.17/1.52  --abstr_cl_out                          false
% 7.17/1.52  
% 7.17/1.52  ------ Global Options
% 7.17/1.52  
% 7.17/1.52  --schedule                              default
% 7.17/1.52  --add_important_lit                     false
% 7.17/1.52  --prop_solver_per_cl                    1000
% 7.17/1.52  --min_unsat_core                        false
% 7.17/1.52  --soft_assumptions                      false
% 7.17/1.52  --soft_lemma_size                       3
% 7.17/1.52  --prop_impl_unit_size                   0
% 7.17/1.52  --prop_impl_unit                        []
% 7.17/1.52  --share_sel_clauses                     true
% 7.17/1.52  --reset_solvers                         false
% 7.17/1.52  --bc_imp_inh                            [conj_cone]
% 7.17/1.52  --conj_cone_tolerance                   3.
% 7.17/1.52  --extra_neg_conj                        none
% 7.17/1.52  --large_theory_mode                     true
% 7.17/1.52  --prolific_symb_bound                   200
% 7.17/1.52  --lt_threshold                          2000
% 7.17/1.52  --clause_weak_htbl                      true
% 7.17/1.52  --gc_record_bc_elim                     false
% 7.17/1.52  
% 7.17/1.52  ------ Preprocessing Options
% 7.17/1.52  
% 7.17/1.52  --preprocessing_flag                    true
% 7.17/1.52  --time_out_prep_mult                    0.1
% 7.17/1.52  --splitting_mode                        input
% 7.17/1.52  --splitting_grd                         true
% 7.17/1.52  --splitting_cvd                         false
% 7.17/1.52  --splitting_cvd_svl                     false
% 7.17/1.52  --splitting_nvd                         32
% 7.17/1.52  --sub_typing                            true
% 7.17/1.52  --prep_gs_sim                           true
% 7.17/1.52  --prep_unflatten                        true
% 7.17/1.52  --prep_res_sim                          true
% 7.17/1.52  --prep_upred                            true
% 7.17/1.52  --prep_sem_filter                       exhaustive
% 7.17/1.52  --prep_sem_filter_out                   false
% 7.17/1.52  --pred_elim                             true
% 7.17/1.52  --res_sim_input                         true
% 7.17/1.52  --eq_ax_congr_red                       true
% 7.17/1.52  --pure_diseq_elim                       true
% 7.17/1.52  --brand_transform                       false
% 7.17/1.52  --non_eq_to_eq                          false
% 7.17/1.52  --prep_def_merge                        true
% 7.17/1.52  --prep_def_merge_prop_impl              false
% 7.17/1.52  --prep_def_merge_mbd                    true
% 7.17/1.52  --prep_def_merge_tr_red                 false
% 7.17/1.52  --prep_def_merge_tr_cl                  false
% 7.17/1.52  --smt_preprocessing                     true
% 7.17/1.52  --smt_ac_axioms                         fast
% 7.17/1.52  --preprocessed_out                      false
% 7.17/1.52  --preprocessed_stats                    false
% 7.17/1.52  
% 7.17/1.52  ------ Abstraction refinement Options
% 7.17/1.52  
% 7.17/1.52  --abstr_ref                             []
% 7.17/1.52  --abstr_ref_prep                        false
% 7.17/1.52  --abstr_ref_until_sat                   false
% 7.17/1.52  --abstr_ref_sig_restrict                funpre
% 7.17/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.17/1.52  --abstr_ref_under                       []
% 7.17/1.52  
% 7.17/1.52  ------ SAT Options
% 7.17/1.52  
% 7.17/1.52  --sat_mode                              false
% 7.17/1.52  --sat_fm_restart_options                ""
% 7.17/1.52  --sat_gr_def                            false
% 7.17/1.52  --sat_epr_types                         true
% 7.17/1.52  --sat_non_cyclic_types                  false
% 7.17/1.52  --sat_finite_models                     false
% 7.17/1.52  --sat_fm_lemmas                         false
% 7.17/1.52  --sat_fm_prep                           false
% 7.17/1.52  --sat_fm_uc_incr                        true
% 7.17/1.52  --sat_out_model                         small
% 7.17/1.52  --sat_out_clauses                       false
% 7.17/1.52  
% 7.17/1.52  ------ QBF Options
% 7.17/1.52  
% 7.17/1.52  --qbf_mode                              false
% 7.17/1.52  --qbf_elim_univ                         false
% 7.17/1.52  --qbf_dom_inst                          none
% 7.17/1.52  --qbf_dom_pre_inst                      false
% 7.17/1.52  --qbf_sk_in                             false
% 7.17/1.52  --qbf_pred_elim                         true
% 7.17/1.52  --qbf_split                             512
% 7.17/1.52  
% 7.17/1.52  ------ BMC1 Options
% 7.17/1.52  
% 7.17/1.52  --bmc1_incremental                      false
% 7.17/1.52  --bmc1_axioms                           reachable_all
% 7.17/1.52  --bmc1_min_bound                        0
% 7.17/1.52  --bmc1_max_bound                        -1
% 7.17/1.52  --bmc1_max_bound_default                -1
% 7.17/1.52  --bmc1_symbol_reachability              true
% 7.17/1.52  --bmc1_property_lemmas                  false
% 7.17/1.52  --bmc1_k_induction                      false
% 7.17/1.52  --bmc1_non_equiv_states                 false
% 7.17/1.52  --bmc1_deadlock                         false
% 7.17/1.52  --bmc1_ucm                              false
% 7.17/1.52  --bmc1_add_unsat_core                   none
% 7.17/1.52  --bmc1_unsat_core_children              false
% 7.17/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.17/1.52  --bmc1_out_stat                         full
% 7.17/1.52  --bmc1_ground_init                      false
% 7.17/1.52  --bmc1_pre_inst_next_state              false
% 7.17/1.52  --bmc1_pre_inst_state                   false
% 7.17/1.52  --bmc1_pre_inst_reach_state             false
% 7.17/1.52  --bmc1_out_unsat_core                   false
% 7.17/1.52  --bmc1_aig_witness_out                  false
% 7.17/1.52  --bmc1_verbose                          false
% 7.17/1.52  --bmc1_dump_clauses_tptp                false
% 7.17/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.17/1.52  --bmc1_dump_file                        -
% 7.17/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.17/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.17/1.52  --bmc1_ucm_extend_mode                  1
% 7.17/1.52  --bmc1_ucm_init_mode                    2
% 7.17/1.52  --bmc1_ucm_cone_mode                    none
% 7.17/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.17/1.52  --bmc1_ucm_relax_model                  4
% 7.17/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.17/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.17/1.52  --bmc1_ucm_layered_model                none
% 7.17/1.52  --bmc1_ucm_max_lemma_size               10
% 7.17/1.52  
% 7.17/1.52  ------ AIG Options
% 7.17/1.52  
% 7.17/1.52  --aig_mode                              false
% 7.17/1.52  
% 7.17/1.52  ------ Instantiation Options
% 7.17/1.52  
% 7.17/1.52  --instantiation_flag                    true
% 7.17/1.52  --inst_sos_flag                         false
% 7.17/1.52  --inst_sos_phase                        true
% 7.17/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.17/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.17/1.52  --inst_lit_sel_side                     num_symb
% 7.17/1.52  --inst_solver_per_active                1400
% 7.17/1.52  --inst_solver_calls_frac                1.
% 7.17/1.52  --inst_passive_queue_type               priority_queues
% 7.17/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.17/1.52  --inst_passive_queues_freq              [25;2]
% 7.17/1.52  --inst_dismatching                      true
% 7.17/1.52  --inst_eager_unprocessed_to_passive     true
% 7.17/1.52  --inst_prop_sim_given                   true
% 7.17/1.52  --inst_prop_sim_new                     false
% 7.17/1.52  --inst_subs_new                         false
% 7.17/1.52  --inst_eq_res_simp                      false
% 7.17/1.52  --inst_subs_given                       false
% 7.17/1.52  --inst_orphan_elimination               true
% 7.17/1.52  --inst_learning_loop_flag               true
% 7.17/1.52  --inst_learning_start                   3000
% 7.17/1.52  --inst_learning_factor                  2
% 7.17/1.52  --inst_start_prop_sim_after_learn       3
% 7.17/1.52  --inst_sel_renew                        solver
% 7.17/1.52  --inst_lit_activity_flag                true
% 7.17/1.52  --inst_restr_to_given                   false
% 7.17/1.52  --inst_activity_threshold               500
% 7.17/1.52  --inst_out_proof                        true
% 7.17/1.52  
% 7.17/1.52  ------ Resolution Options
% 7.17/1.52  
% 7.17/1.52  --resolution_flag                       true
% 7.17/1.52  --res_lit_sel                           adaptive
% 7.17/1.52  --res_lit_sel_side                      none
% 7.17/1.52  --res_ordering                          kbo
% 7.17/1.52  --res_to_prop_solver                    active
% 7.17/1.52  --res_prop_simpl_new                    false
% 7.17/1.52  --res_prop_simpl_given                  true
% 7.17/1.52  --res_passive_queue_type                priority_queues
% 7.17/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.17/1.52  --res_passive_queues_freq               [15;5]
% 7.17/1.52  --res_forward_subs                      full
% 7.17/1.52  --res_backward_subs                     full
% 7.17/1.52  --res_forward_subs_resolution           true
% 7.17/1.52  --res_backward_subs_resolution          true
% 7.17/1.52  --res_orphan_elimination                true
% 7.17/1.52  --res_time_limit                        2.
% 7.17/1.52  --res_out_proof                         true
% 7.17/1.52  
% 7.17/1.52  ------ Superposition Options
% 7.17/1.52  
% 7.17/1.52  --superposition_flag                    true
% 7.17/1.52  --sup_passive_queue_type                priority_queues
% 7.17/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.17/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.17/1.52  --demod_completeness_check              fast
% 7.17/1.52  --demod_use_ground                      true
% 7.17/1.52  --sup_to_prop_solver                    passive
% 7.17/1.52  --sup_prop_simpl_new                    true
% 7.17/1.52  --sup_prop_simpl_given                  true
% 7.17/1.52  --sup_fun_splitting                     false
% 7.17/1.52  --sup_smt_interval                      50000
% 7.17/1.52  
% 7.17/1.52  ------ Superposition Simplification Setup
% 7.17/1.52  
% 7.17/1.52  --sup_indices_passive                   []
% 7.17/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.17/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.52  --sup_full_bw                           [BwDemod]
% 7.17/1.52  --sup_immed_triv                        [TrivRules]
% 7.17/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.17/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.52  --sup_immed_bw_main                     []
% 7.17/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.17/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.52  
% 7.17/1.52  ------ Combination Options
% 7.17/1.52  
% 7.17/1.52  --comb_res_mult                         3
% 7.17/1.52  --comb_sup_mult                         2
% 7.17/1.52  --comb_inst_mult                        10
% 7.17/1.52  
% 7.17/1.52  ------ Debug Options
% 7.17/1.52  
% 7.17/1.52  --dbg_backtrace                         false
% 7.17/1.52  --dbg_dump_prop_clauses                 false
% 7.17/1.52  --dbg_dump_prop_clauses_file            -
% 7.17/1.52  --dbg_out_stat                          false
% 7.17/1.52  ------ Parsing...
% 7.17/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.17/1.52  
% 7.17/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.17/1.52  
% 7.17/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.17/1.52  
% 7.17/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.17/1.52  ------ Proving...
% 7.17/1.52  ------ Problem Properties 
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  clauses                                 20
% 7.17/1.52  conjectures                             5
% 7.17/1.52  EPR                                     6
% 7.17/1.52  Horn                                    13
% 7.17/1.52  unary                                   6
% 7.17/1.52  binary                                  5
% 7.17/1.52  lits                                    45
% 7.17/1.52  lits eq                                 4
% 7.17/1.52  fd_pure                                 0
% 7.17/1.52  fd_pseudo                               0
% 7.17/1.52  fd_cond                                 0
% 7.17/1.52  fd_pseudo_cond                          0
% 7.17/1.52  AC symbols                              0
% 7.17/1.52  
% 7.17/1.52  ------ Schedule dynamic 5 is on 
% 7.17/1.52  
% 7.17/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  ------ 
% 7.17/1.52  Current options:
% 7.17/1.52  ------ 
% 7.17/1.52  
% 7.17/1.52  ------ Input Options
% 7.17/1.52  
% 7.17/1.52  --out_options                           all
% 7.17/1.52  --tptp_safe_out                         true
% 7.17/1.52  --problem_path                          ""
% 7.17/1.52  --include_path                          ""
% 7.17/1.52  --clausifier                            res/vclausify_rel
% 7.17/1.52  --clausifier_options                    --mode clausify
% 7.17/1.52  --stdin                                 false
% 7.17/1.52  --stats_out                             all
% 7.17/1.52  
% 7.17/1.52  ------ General Options
% 7.17/1.52  
% 7.17/1.52  --fof                                   false
% 7.17/1.52  --time_out_real                         305.
% 7.17/1.52  --time_out_virtual                      -1.
% 7.17/1.52  --symbol_type_check                     false
% 7.17/1.52  --clausify_out                          false
% 7.17/1.52  --sig_cnt_out                           false
% 7.17/1.52  --trig_cnt_out                          false
% 7.17/1.52  --trig_cnt_out_tolerance                1.
% 7.17/1.52  --trig_cnt_out_sk_spl                   false
% 7.17/1.52  --abstr_cl_out                          false
% 7.17/1.52  
% 7.17/1.52  ------ Global Options
% 7.17/1.52  
% 7.17/1.52  --schedule                              default
% 7.17/1.52  --add_important_lit                     false
% 7.17/1.52  --prop_solver_per_cl                    1000
% 7.17/1.52  --min_unsat_core                        false
% 7.17/1.52  --soft_assumptions                      false
% 7.17/1.52  --soft_lemma_size                       3
% 7.17/1.52  --prop_impl_unit_size                   0
% 7.17/1.52  --prop_impl_unit                        []
% 7.17/1.52  --share_sel_clauses                     true
% 7.17/1.52  --reset_solvers                         false
% 7.17/1.52  --bc_imp_inh                            [conj_cone]
% 7.17/1.52  --conj_cone_tolerance                   3.
% 7.17/1.52  --extra_neg_conj                        none
% 7.17/1.52  --large_theory_mode                     true
% 7.17/1.52  --prolific_symb_bound                   200
% 7.17/1.52  --lt_threshold                          2000
% 7.17/1.52  --clause_weak_htbl                      true
% 7.17/1.52  --gc_record_bc_elim                     false
% 7.17/1.52  
% 7.17/1.52  ------ Preprocessing Options
% 7.17/1.52  
% 7.17/1.52  --preprocessing_flag                    true
% 7.17/1.52  --time_out_prep_mult                    0.1
% 7.17/1.52  --splitting_mode                        input
% 7.17/1.52  --splitting_grd                         true
% 7.17/1.52  --splitting_cvd                         false
% 7.17/1.52  --splitting_cvd_svl                     false
% 7.17/1.52  --splitting_nvd                         32
% 7.17/1.52  --sub_typing                            true
% 7.17/1.52  --prep_gs_sim                           true
% 7.17/1.52  --prep_unflatten                        true
% 7.17/1.52  --prep_res_sim                          true
% 7.17/1.52  --prep_upred                            true
% 7.17/1.52  --prep_sem_filter                       exhaustive
% 7.17/1.52  --prep_sem_filter_out                   false
% 7.17/1.52  --pred_elim                             true
% 7.17/1.52  --res_sim_input                         true
% 7.17/1.52  --eq_ax_congr_red                       true
% 7.17/1.52  --pure_diseq_elim                       true
% 7.17/1.52  --brand_transform                       false
% 7.17/1.52  --non_eq_to_eq                          false
% 7.17/1.52  --prep_def_merge                        true
% 7.17/1.52  --prep_def_merge_prop_impl              false
% 7.17/1.52  --prep_def_merge_mbd                    true
% 7.17/1.52  --prep_def_merge_tr_red                 false
% 7.17/1.52  --prep_def_merge_tr_cl                  false
% 7.17/1.52  --smt_preprocessing                     true
% 7.17/1.52  --smt_ac_axioms                         fast
% 7.17/1.52  --preprocessed_out                      false
% 7.17/1.52  --preprocessed_stats                    false
% 7.17/1.52  
% 7.17/1.52  ------ Abstraction refinement Options
% 7.17/1.52  
% 7.17/1.52  --abstr_ref                             []
% 7.17/1.52  --abstr_ref_prep                        false
% 7.17/1.52  --abstr_ref_until_sat                   false
% 7.17/1.52  --abstr_ref_sig_restrict                funpre
% 7.17/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.17/1.52  --abstr_ref_under                       []
% 7.17/1.52  
% 7.17/1.52  ------ SAT Options
% 7.17/1.52  
% 7.17/1.52  --sat_mode                              false
% 7.17/1.52  --sat_fm_restart_options                ""
% 7.17/1.52  --sat_gr_def                            false
% 7.17/1.52  --sat_epr_types                         true
% 7.17/1.52  --sat_non_cyclic_types                  false
% 7.17/1.52  --sat_finite_models                     false
% 7.17/1.52  --sat_fm_lemmas                         false
% 7.17/1.52  --sat_fm_prep                           false
% 7.17/1.52  --sat_fm_uc_incr                        true
% 7.17/1.52  --sat_out_model                         small
% 7.17/1.52  --sat_out_clauses                       false
% 7.17/1.52  
% 7.17/1.52  ------ QBF Options
% 7.17/1.52  
% 7.17/1.52  --qbf_mode                              false
% 7.17/1.52  --qbf_elim_univ                         false
% 7.17/1.52  --qbf_dom_inst                          none
% 7.17/1.52  --qbf_dom_pre_inst                      false
% 7.17/1.52  --qbf_sk_in                             false
% 7.17/1.52  --qbf_pred_elim                         true
% 7.17/1.52  --qbf_split                             512
% 7.17/1.52  
% 7.17/1.52  ------ BMC1 Options
% 7.17/1.52  
% 7.17/1.52  --bmc1_incremental                      false
% 7.17/1.52  --bmc1_axioms                           reachable_all
% 7.17/1.52  --bmc1_min_bound                        0
% 7.17/1.52  --bmc1_max_bound                        -1
% 7.17/1.52  --bmc1_max_bound_default                -1
% 7.17/1.52  --bmc1_symbol_reachability              true
% 7.17/1.52  --bmc1_property_lemmas                  false
% 7.17/1.52  --bmc1_k_induction                      false
% 7.17/1.52  --bmc1_non_equiv_states                 false
% 7.17/1.52  --bmc1_deadlock                         false
% 7.17/1.52  --bmc1_ucm                              false
% 7.17/1.52  --bmc1_add_unsat_core                   none
% 7.17/1.52  --bmc1_unsat_core_children              false
% 7.17/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.17/1.52  --bmc1_out_stat                         full
% 7.17/1.52  --bmc1_ground_init                      false
% 7.17/1.52  --bmc1_pre_inst_next_state              false
% 7.17/1.52  --bmc1_pre_inst_state                   false
% 7.17/1.52  --bmc1_pre_inst_reach_state             false
% 7.17/1.52  --bmc1_out_unsat_core                   false
% 7.17/1.52  --bmc1_aig_witness_out                  false
% 7.17/1.52  --bmc1_verbose                          false
% 7.17/1.52  --bmc1_dump_clauses_tptp                false
% 7.17/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.17/1.52  --bmc1_dump_file                        -
% 7.17/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.17/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.17/1.52  --bmc1_ucm_extend_mode                  1
% 7.17/1.52  --bmc1_ucm_init_mode                    2
% 7.17/1.52  --bmc1_ucm_cone_mode                    none
% 7.17/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.17/1.52  --bmc1_ucm_relax_model                  4
% 7.17/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.17/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.17/1.52  --bmc1_ucm_layered_model                none
% 7.17/1.52  --bmc1_ucm_max_lemma_size               10
% 7.17/1.52  
% 7.17/1.52  ------ AIG Options
% 7.17/1.52  
% 7.17/1.52  --aig_mode                              false
% 7.17/1.52  
% 7.17/1.52  ------ Instantiation Options
% 7.17/1.52  
% 7.17/1.52  --instantiation_flag                    true
% 7.17/1.52  --inst_sos_flag                         false
% 7.17/1.52  --inst_sos_phase                        true
% 7.17/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.17/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.17/1.52  --inst_lit_sel_side                     none
% 7.17/1.52  --inst_solver_per_active                1400
% 7.17/1.52  --inst_solver_calls_frac                1.
% 7.17/1.52  --inst_passive_queue_type               priority_queues
% 7.17/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.17/1.52  --inst_passive_queues_freq              [25;2]
% 7.17/1.52  --inst_dismatching                      true
% 7.17/1.52  --inst_eager_unprocessed_to_passive     true
% 7.17/1.52  --inst_prop_sim_given                   true
% 7.17/1.52  --inst_prop_sim_new                     false
% 7.17/1.52  --inst_subs_new                         false
% 7.17/1.52  --inst_eq_res_simp                      false
% 7.17/1.52  --inst_subs_given                       false
% 7.17/1.52  --inst_orphan_elimination               true
% 7.17/1.52  --inst_learning_loop_flag               true
% 7.17/1.52  --inst_learning_start                   3000
% 7.17/1.52  --inst_learning_factor                  2
% 7.17/1.52  --inst_start_prop_sim_after_learn       3
% 7.17/1.52  --inst_sel_renew                        solver
% 7.17/1.52  --inst_lit_activity_flag                true
% 7.17/1.52  --inst_restr_to_given                   false
% 7.17/1.52  --inst_activity_threshold               500
% 7.17/1.52  --inst_out_proof                        true
% 7.17/1.52  
% 7.17/1.52  ------ Resolution Options
% 7.17/1.52  
% 7.17/1.52  --resolution_flag                       false
% 7.17/1.52  --res_lit_sel                           adaptive
% 7.17/1.52  --res_lit_sel_side                      none
% 7.17/1.52  --res_ordering                          kbo
% 7.17/1.52  --res_to_prop_solver                    active
% 7.17/1.52  --res_prop_simpl_new                    false
% 7.17/1.52  --res_prop_simpl_given                  true
% 7.17/1.52  --res_passive_queue_type                priority_queues
% 7.17/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.17/1.52  --res_passive_queues_freq               [15;5]
% 7.17/1.52  --res_forward_subs                      full
% 7.17/1.52  --res_backward_subs                     full
% 7.17/1.52  --res_forward_subs_resolution           true
% 7.17/1.52  --res_backward_subs_resolution          true
% 7.17/1.52  --res_orphan_elimination                true
% 7.17/1.52  --res_time_limit                        2.
% 7.17/1.52  --res_out_proof                         true
% 7.17/1.52  
% 7.17/1.52  ------ Superposition Options
% 7.17/1.52  
% 7.17/1.52  --superposition_flag                    true
% 7.17/1.52  --sup_passive_queue_type                priority_queues
% 7.17/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.17/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.17/1.52  --demod_completeness_check              fast
% 7.17/1.52  --demod_use_ground                      true
% 7.17/1.52  --sup_to_prop_solver                    passive
% 7.17/1.52  --sup_prop_simpl_new                    true
% 7.17/1.52  --sup_prop_simpl_given                  true
% 7.17/1.52  --sup_fun_splitting                     false
% 7.17/1.52  --sup_smt_interval                      50000
% 7.17/1.52  
% 7.17/1.52  ------ Superposition Simplification Setup
% 7.17/1.52  
% 7.17/1.52  --sup_indices_passive                   []
% 7.17/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.17/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.52  --sup_full_bw                           [BwDemod]
% 7.17/1.52  --sup_immed_triv                        [TrivRules]
% 7.17/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.17/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.52  --sup_immed_bw_main                     []
% 7.17/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.17/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.52  
% 7.17/1.52  ------ Combination Options
% 7.17/1.52  
% 7.17/1.52  --comb_res_mult                         3
% 7.17/1.52  --comb_sup_mult                         2
% 7.17/1.52  --comb_inst_mult                        10
% 7.17/1.52  
% 7.17/1.52  ------ Debug Options
% 7.17/1.52  
% 7.17/1.52  --dbg_backtrace                         false
% 7.17/1.52  --dbg_dump_prop_clauses                 false
% 7.17/1.52  --dbg_dump_prop_clauses_file            -
% 7.17/1.52  --dbg_out_stat                          false
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  ------ Proving...
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  % SZS status Theorem for theBenchmark.p
% 7.17/1.52  
% 7.17/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.17/1.52  
% 7.17/1.52  fof(f4,axiom,(
% 7.17/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f15,plain,(
% 7.17/1.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f4])).
% 7.17/1.52  
% 7.17/1.52  fof(f52,plain,(
% 7.17/1.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.17/1.52    inference(cnf_transformation,[],[f15])).
% 7.17/1.52  
% 7.17/1.52  fof(f2,axiom,(
% 7.17/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f14,plain,(
% 7.17/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f2])).
% 7.17/1.52  
% 7.17/1.52  fof(f34,plain,(
% 7.17/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.17/1.52    inference(nnf_transformation,[],[f14])).
% 7.17/1.52  
% 7.17/1.52  fof(f35,plain,(
% 7.17/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.17/1.52    inference(rectify,[],[f34])).
% 7.17/1.52  
% 7.17/1.52  fof(f36,plain,(
% 7.17/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.17/1.52    introduced(choice_axiom,[])).
% 7.17/1.52  
% 7.17/1.52  fof(f37,plain,(
% 7.17/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.17/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 7.17/1.52  
% 7.17/1.52  fof(f49,plain,(
% 7.17/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f37])).
% 7.17/1.52  
% 7.17/1.52  fof(f50,plain,(
% 7.17/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f37])).
% 7.17/1.52  
% 7.17/1.52  fof(f12,conjecture,(
% 7.17/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f13,negated_conjecture,(
% 7.17/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 7.17/1.52    inference(negated_conjecture,[],[f12])).
% 7.17/1.52  
% 7.17/1.52  fof(f28,plain,(
% 7.17/1.52    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f13])).
% 7.17/1.52  
% 7.17/1.52  fof(f29,plain,(
% 7.17/1.52    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.17/1.52    inference(flattening,[],[f28])).
% 7.17/1.52  
% 7.17/1.52  fof(f44,plain,(
% 7.17/1.52    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.17/1.52    introduced(choice_axiom,[])).
% 7.17/1.52  
% 7.17/1.52  fof(f43,plain,(
% 7.17/1.52    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.17/1.52    introduced(choice_axiom,[])).
% 7.17/1.52  
% 7.17/1.52  fof(f42,plain,(
% 7.17/1.52    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 7.17/1.52    introduced(choice_axiom,[])).
% 7.17/1.52  
% 7.17/1.52  fof(f45,plain,(
% 7.17/1.52    ((k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 7.17/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f44,f43,f42])).
% 7.17/1.52  
% 7.17/1.52  fof(f68,plain,(
% 7.17/1.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f10,axiom,(
% 7.17/1.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f24,plain,(
% 7.17/1.52    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f10])).
% 7.17/1.52  
% 7.17/1.52  fof(f25,plain,(
% 7.17/1.52    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.17/1.52    inference(flattening,[],[f24])).
% 7.17/1.52  
% 7.17/1.52  fof(f58,plain,(
% 7.17/1.52    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f25])).
% 7.17/1.52  
% 7.17/1.52  fof(f3,axiom,(
% 7.17/1.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f51,plain,(
% 7.17/1.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f3])).
% 7.17/1.52  
% 7.17/1.52  fof(f71,plain,(
% 7.17/1.52    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.17/1.52    inference(definition_unfolding,[],[f58,f51])).
% 7.17/1.52  
% 7.17/1.52  fof(f11,axiom,(
% 7.17/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f26,plain,(
% 7.17/1.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f11])).
% 7.17/1.52  
% 7.17/1.52  fof(f27,plain,(
% 7.17/1.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.17/1.52    inference(flattening,[],[f26])).
% 7.17/1.52  
% 7.17/1.52  fof(f38,plain,(
% 7.17/1.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.17/1.52    inference(nnf_transformation,[],[f27])).
% 7.17/1.52  
% 7.17/1.52  fof(f39,plain,(
% 7.17/1.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.17/1.52    inference(rectify,[],[f38])).
% 7.17/1.52  
% 7.17/1.52  fof(f40,plain,(
% 7.17/1.52    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.17/1.52    introduced(choice_axiom,[])).
% 7.17/1.52  
% 7.17/1.52  fof(f41,plain,(
% 7.17/1.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.17/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 7.17/1.52  
% 7.17/1.52  fof(f59,plain,(
% 7.17/1.52    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f41])).
% 7.17/1.52  
% 7.17/1.52  fof(f64,plain,(
% 7.17/1.52    v2_pre_topc(sK3)),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f63,plain,(
% 7.17/1.52    ~v2_struct_0(sK3)),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f65,plain,(
% 7.17/1.52    l1_pre_topc(sK3)),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f9,axiom,(
% 7.17/1.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f22,plain,(
% 7.17/1.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f9])).
% 7.17/1.52  
% 7.17/1.52  fof(f23,plain,(
% 7.17/1.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.17/1.52    inference(flattening,[],[f22])).
% 7.17/1.52  
% 7.17/1.52  fof(f57,plain,(
% 7.17/1.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f23])).
% 7.17/1.52  
% 7.17/1.52  fof(f5,axiom,(
% 7.17/1.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f16,plain,(
% 7.17/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.17/1.52    inference(ennf_transformation,[],[f5])).
% 7.17/1.52  
% 7.17/1.52  fof(f53,plain,(
% 7.17/1.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f16])).
% 7.17/1.52  
% 7.17/1.52  fof(f1,axiom,(
% 7.17/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f30,plain,(
% 7.17/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.17/1.52    inference(nnf_transformation,[],[f1])).
% 7.17/1.52  
% 7.17/1.52  fof(f31,plain,(
% 7.17/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.17/1.52    inference(rectify,[],[f30])).
% 7.17/1.52  
% 7.17/1.52  fof(f32,plain,(
% 7.17/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.17/1.52    introduced(choice_axiom,[])).
% 7.17/1.52  
% 7.17/1.52  fof(f33,plain,(
% 7.17/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.17/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.17/1.52  
% 7.17/1.52  fof(f46,plain,(
% 7.17/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f33])).
% 7.17/1.52  
% 7.17/1.52  fof(f7,axiom,(
% 7.17/1.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f19,plain,(
% 7.17/1.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.17/1.52    inference(ennf_transformation,[],[f7])).
% 7.17/1.52  
% 7.17/1.52  fof(f55,plain,(
% 7.17/1.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f19])).
% 7.17/1.52  
% 7.17/1.52  fof(f8,axiom,(
% 7.17/1.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.17/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.52  
% 7.17/1.52  fof(f20,plain,(
% 7.17/1.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.17/1.52    inference(ennf_transformation,[],[f8])).
% 7.17/1.52  
% 7.17/1.52  fof(f21,plain,(
% 7.17/1.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.17/1.52    inference(flattening,[],[f20])).
% 7.17/1.52  
% 7.17/1.52  fof(f56,plain,(
% 7.17/1.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.17/1.52    inference(cnf_transformation,[],[f21])).
% 7.17/1.52  
% 7.17/1.52  fof(f70,plain,(
% 7.17/1.52    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f69,plain,(
% 7.17/1.52    r2_hidden(sK5,sK4)),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f67,plain,(
% 7.17/1.52    v2_tex_2(sK4,sK3)),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  fof(f66,plain,(
% 7.17/1.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 7.17/1.52    inference(cnf_transformation,[],[f45])).
% 7.17/1.52  
% 7.17/1.52  cnf(c_5,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.17/1.52      | ~ r2_hidden(X2,X0)
% 7.17/1.52      | r2_hidden(X2,X1) ),
% 7.17/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_6180,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.17/1.52      | ~ r2_hidden(sK1(X0,sK4),X0)
% 7.17/1.52      | r2_hidden(sK1(X0,sK4),X1) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_18810,plain,
% 7.17/1.52      ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
% 7.17/1.52      | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5))
% 7.17/1.52      | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_6180]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_3,plain,
% 7.17/1.52      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.17/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1783,plain,
% 7.17/1.52      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_5373,plain,
% 7.17/1.52      ( r1_tarski(k2_tarski(sK5,sK5),sK4)
% 7.17/1.52      | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5)) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1783]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2,plain,
% 7.17/1.52      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 7.17/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1784,plain,
% 7.17/1.52      ( r1_tarski(X0,sK4) | ~ r2_hidden(sK1(X0,sK4),sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_5374,plain,
% 7.17/1.52      ( r1_tarski(k2_tarski(sK5,sK5),sK4)
% 7.17/1.52      | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1784]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1145,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.17/1.52      theory(equality) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2089,plain,
% 7.17/1.52      ( m1_subset_1(X0,X1)
% 7.17/1.52      | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.17/1.52      | X0 != k6_domain_1(sK4,sK5)
% 7.17/1.52      | X1 != k1_zfmisc_1(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1145]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2871,plain,
% 7.17/1.52      ( m1_subset_1(X0,k1_zfmisc_1(sK4))
% 7.17/1.52      | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.17/1.52      | X0 != k6_domain_1(sK4,sK5)
% 7.17/1.52      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_2089]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_4564,plain,
% 7.17/1.52      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
% 7.17/1.52      | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.17/1.52      | k2_tarski(sK5,sK5) != k6_domain_1(sK4,sK5)
% 7.17/1.52      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_2871]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1143,plain,
% 7.17/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.17/1.52      theory(equality) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1793,plain,
% 7.17/1.52      ( ~ r1_tarski(X0,sK4) | r1_tarski(X1,sK4) | X1 != X0 ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1143]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2299,plain,
% 7.17/1.52      ( ~ r1_tarski(X0,sK4)
% 7.17/1.52      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 7.17/1.52      | k6_domain_1(u1_struct_0(sK3),sK5) != X0 ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1793]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_3989,plain,
% 7.17/1.52      ( ~ r1_tarski(k2_tarski(sK5,sK5),sK4)
% 7.17/1.52      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 7.17/1.52      | k6_domain_1(u1_struct_0(sK3),sK5) != k2_tarski(sK5,sK5) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_2299]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1139,plain,( X0 = X0 ),theory(equality) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2872,plain,
% 7.17/1.52      ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1139]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_18,negated_conjecture,
% 7.17/1.52      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.17/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1513,plain,
% 7.17/1.52      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.17/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_11,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,X1)
% 7.17/1.52      | v1_xboole_0(X1)
% 7.17/1.52      | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
% 7.17/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1515,plain,
% 7.17/1.52      ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
% 7.17/1.52      | m1_subset_1(X0,X1) != iProver_top
% 7.17/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.17/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2446,plain,
% 7.17/1.52      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
% 7.17/1.52      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.17/1.52      inference(superposition,[status(thm)],[c_1513,c_1515]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_15,plain,
% 7.17/1.52      ( ~ v2_tex_2(X0,X1)
% 7.17/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.52      | ~ r1_tarski(X2,X0)
% 7.17/1.52      | ~ v2_pre_topc(X1)
% 7.17/1.52      | v2_struct_0(X1)
% 7.17/1.52      | ~ l1_pre_topc(X1)
% 7.17/1.52      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 7.17/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_22,negated_conjecture,
% 7.17/1.52      ( v2_pre_topc(sK3) ),
% 7.17/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_276,plain,
% 7.17/1.52      ( ~ v2_tex_2(X0,X1)
% 7.17/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.52      | ~ r1_tarski(X2,X0)
% 7.17/1.52      | v2_struct_0(X1)
% 7.17/1.52      | ~ l1_pre_topc(X1)
% 7.17/1.52      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 7.17/1.52      | sK3 != X1 ),
% 7.17/1.52      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_277,plain,
% 7.17/1.52      ( ~ v2_tex_2(X0,sK3)
% 7.17/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ r1_tarski(X1,X0)
% 7.17/1.52      | v2_struct_0(sK3)
% 7.17/1.52      | ~ l1_pre_topc(sK3)
% 7.17/1.52      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 7.17/1.52      inference(unflattening,[status(thm)],[c_276]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_23,negated_conjecture,
% 7.17/1.52      ( ~ v2_struct_0(sK3) ),
% 7.17/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_21,negated_conjecture,
% 7.17/1.52      ( l1_pre_topc(sK3) ),
% 7.17/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_281,plain,
% 7.17/1.52      ( ~ v2_tex_2(X0,sK3)
% 7.17/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ r1_tarski(X1,X0)
% 7.17/1.52      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 7.17/1.52      inference(global_propositional_subsumption,
% 7.17/1.52                [status(thm)],
% 7.17/1.52                [c_277,c_23,c_21]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_282,plain,
% 7.17/1.52      ( ~ v2_tex_2(X0,sK3)
% 7.17/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ r1_tarski(X1,X0)
% 7.17/1.52      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 7.17/1.52      inference(renaming,[status(thm)],[c_281]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1661,plain,
% 7.17/1.52      ( ~ v2_tex_2(sK4,sK3)
% 7.17/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ r1_tarski(X0,sK4)
% 7.17/1.52      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_282]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_2053,plain,
% 7.17/1.52      ( ~ v2_tex_2(sK4,sK3)
% 7.17/1.52      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 7.17/1.52      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1661]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1733,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,sK4)
% 7.17/1.52      | v1_xboole_0(sK4)
% 7.17/1.52      | k2_tarski(X0,X0) = k6_domain_1(sK4,X0) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_11]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1994,plain,
% 7.17/1.52      ( ~ m1_subset_1(sK5,sK4)
% 7.17/1.52      | v1_xboole_0(sK4)
% 7.17/1.52      | k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1733]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_10,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,X1)
% 7.17/1.52      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 7.17/1.52      | v1_xboole_0(X1) ),
% 7.17/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1734,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,sK4)
% 7.17/1.52      | m1_subset_1(k6_domain_1(sK4,X0),k1_zfmisc_1(sK4))
% 7.17/1.52      | v1_xboole_0(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1959,plain,
% 7.17/1.52      ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.17/1.52      | ~ m1_subset_1(sK5,sK4)
% 7.17/1.52      | v1_xboole_0(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1734]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1698,plain,
% 7.17/1.52      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.17/1.52      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | v1_xboole_0(u1_struct_0(sK3)) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1932,plain,
% 7.17/1.52      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.52      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 7.17/1.52      | v1_xboole_0(u1_struct_0(sK3)) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1698]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1777,plain,
% 7.17/1.52      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1139]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1140,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1701,plain,
% 7.17/1.52      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
% 7.17/1.52      | k6_domain_1(u1_struct_0(sK3),sK5) != X0
% 7.17/1.52      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1140]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1776,plain,
% 7.17/1.52      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
% 7.17/1.52      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
% 7.17/1.52      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1701]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_6,plain,
% 7.17/1.52      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.17/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1673,plain,
% 7.17/1.52      ( m1_subset_1(sK5,sK4) | ~ r2_hidden(sK5,sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1,plain,
% 7.17/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.17/1.52      inference(cnf_transformation,[],[f46]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_1670,plain,
% 7.17/1.52      ( ~ r2_hidden(sK5,sK4) | ~ v1_xboole_0(sK4) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_8,plain,
% 7.17/1.52      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.17/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_52,plain,
% 7.17/1.52      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.17/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_54,plain,
% 7.17/1.52      ( l1_pre_topc(sK3) != iProver_top
% 7.17/1.52      | l1_struct_0(sK3) = iProver_top ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_52]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_53,plain,
% 7.17/1.52      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_8]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_9,plain,
% 7.17/1.52      ( v2_struct_0(X0)
% 7.17/1.52      | ~ l1_struct_0(X0)
% 7.17/1.52      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.17/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_49,plain,
% 7.17/1.52      ( v2_struct_0(X0) = iProver_top
% 7.17/1.52      | l1_struct_0(X0) != iProver_top
% 7.17/1.52      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 7.17/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_51,plain,
% 7.17/1.52      ( v2_struct_0(sK3) = iProver_top
% 7.17/1.52      | l1_struct_0(sK3) != iProver_top
% 7.17/1.52      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_49]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_50,plain,
% 7.17/1.52      ( v2_struct_0(sK3)
% 7.17/1.52      | ~ l1_struct_0(sK3)
% 7.17/1.52      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.17/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_16,negated_conjecture,
% 7.17/1.52      ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 7.17/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_17,negated_conjecture,
% 7.17/1.52      ( r2_hidden(sK5,sK4) ),
% 7.17/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_19,negated_conjecture,
% 7.17/1.52      ( v2_tex_2(sK4,sK3) ),
% 7.17/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_20,negated_conjecture,
% 7.17/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.17/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_26,plain,
% 7.17/1.52      ( l1_pre_topc(sK3) = iProver_top ),
% 7.17/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(c_24,plain,
% 7.17/1.52      ( v2_struct_0(sK3) != iProver_top ),
% 7.17/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.17/1.52  
% 7.17/1.52  cnf(contradiction,plain,
% 7.17/1.52      ( $false ),
% 7.17/1.52      inference(minisat,
% 7.17/1.52                [status(thm)],
% 7.17/1.52                [c_18810,c_5373,c_5374,c_4564,c_3989,c_2872,c_2446,
% 7.17/1.52                 c_2053,c_1994,c_1959,c_1932,c_1777,c_1776,c_1673,c_1670,
% 7.17/1.52                 c_54,c_53,c_51,c_50,c_16,c_17,c_18,c_19,c_20,c_26,c_21,
% 7.17/1.52                 c_24,c_23]) ).
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.17/1.52  
% 7.17/1.52  ------                               Statistics
% 7.17/1.52  
% 7.17/1.52  ------ General
% 7.17/1.52  
% 7.17/1.52  abstr_ref_over_cycles:                  0
% 7.17/1.52  abstr_ref_under_cycles:                 0
% 7.17/1.52  gc_basic_clause_elim:                   0
% 7.17/1.52  forced_gc_time:                         0
% 7.17/1.52  parsing_time:                           0.007
% 7.17/1.52  unif_index_cands_time:                  0.
% 7.17/1.52  unif_index_add_time:                    0.
% 7.17/1.52  orderings_time:                         0.
% 7.17/1.52  out_proof_time:                         0.009
% 7.17/1.52  total_time:                             0.513
% 7.17/1.52  num_of_symbols:                         52
% 7.17/1.52  num_of_terms:                           13920
% 7.17/1.52  
% 7.17/1.52  ------ Preprocessing
% 7.17/1.52  
% 7.17/1.52  num_of_splits:                          0
% 7.17/1.52  num_of_split_atoms:                     0
% 7.17/1.52  num_of_reused_defs:                     0
% 7.17/1.52  num_eq_ax_congr_red:                    23
% 7.17/1.52  num_of_sem_filtered_clauses:            1
% 7.17/1.52  num_of_subtypes:                        0
% 7.17/1.52  monotx_restored_types:                  0
% 7.17/1.52  sat_num_of_epr_types:                   0
% 7.17/1.52  sat_num_of_non_cyclic_types:            0
% 7.17/1.52  sat_guarded_non_collapsed_types:        0
% 7.17/1.52  num_pure_diseq_elim:                    0
% 7.17/1.52  simp_replaced_by:                       0
% 7.17/1.52  res_preprocessed:                       111
% 7.17/1.52  prep_upred:                             0
% 7.17/1.52  prep_unflattend:                        33
% 7.17/1.52  smt_new_axioms:                         0
% 7.17/1.52  pred_elim_cands:                        5
% 7.17/1.52  pred_elim:                              4
% 7.17/1.52  pred_elim_cl:                           4
% 7.17/1.52  pred_elim_cycles:                       10
% 7.17/1.52  merged_defs:                            0
% 7.17/1.52  merged_defs_ncl:                        0
% 7.17/1.52  bin_hyper_res:                          0
% 7.17/1.52  prep_cycles:                            4
% 7.17/1.52  pred_elim_time:                         0.008
% 7.17/1.52  splitting_time:                         0.
% 7.17/1.52  sem_filter_time:                        0.
% 7.17/1.52  monotx_time:                            0.
% 7.17/1.52  subtype_inf_time:                       0.
% 7.17/1.52  
% 7.17/1.52  ------ Problem properties
% 7.17/1.52  
% 7.17/1.52  clauses:                                20
% 7.17/1.52  conjectures:                            5
% 7.17/1.52  epr:                                    6
% 7.17/1.52  horn:                                   13
% 7.17/1.52  ground:                                 6
% 7.17/1.52  unary:                                  6
% 7.17/1.52  binary:                                 5
% 7.17/1.52  lits:                                   45
% 7.17/1.52  lits_eq:                                4
% 7.17/1.52  fd_pure:                                0
% 7.17/1.52  fd_pseudo:                              0
% 7.17/1.52  fd_cond:                                0
% 7.17/1.52  fd_pseudo_cond:                         0
% 7.17/1.52  ac_symbols:                             0
% 7.17/1.52  
% 7.17/1.52  ------ Propositional Solver
% 7.17/1.52  
% 7.17/1.52  prop_solver_calls:                      31
% 7.17/1.52  prop_fast_solver_calls:                 1466
% 7.17/1.52  smt_solver_calls:                       0
% 7.17/1.52  smt_fast_solver_calls:                  0
% 7.17/1.52  prop_num_of_clauses:                    6466
% 7.17/1.52  prop_preprocess_simplified:             10263
% 7.17/1.52  prop_fo_subsumed:                       37
% 7.17/1.52  prop_solver_time:                       0.
% 7.17/1.52  smt_solver_time:                        0.
% 7.17/1.52  smt_fast_solver_time:                   0.
% 7.17/1.52  prop_fast_solver_time:                  0.
% 7.17/1.52  prop_unsat_core_time:                   0.
% 7.17/1.52  
% 7.17/1.52  ------ QBF
% 7.17/1.52  
% 7.17/1.52  qbf_q_res:                              0
% 7.17/1.52  qbf_num_tautologies:                    0
% 7.17/1.52  qbf_prep_cycles:                        0
% 7.17/1.52  
% 7.17/1.52  ------ BMC1
% 7.17/1.52  
% 7.17/1.52  bmc1_current_bound:                     -1
% 7.17/1.52  bmc1_last_solved_bound:                 -1
% 7.17/1.52  bmc1_unsat_core_size:                   -1
% 7.17/1.52  bmc1_unsat_core_parents_size:           -1
% 7.17/1.52  bmc1_merge_next_fun:                    0
% 7.17/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.17/1.52  
% 7.17/1.52  ------ Instantiation
% 7.17/1.52  
% 7.17/1.52  inst_num_of_clauses:                    1604
% 7.17/1.52  inst_num_in_passive:                    257
% 7.17/1.52  inst_num_in_active:                     918
% 7.17/1.52  inst_num_in_unprocessed:                428
% 7.17/1.52  inst_num_of_loops:                      1032
% 7.17/1.52  inst_num_of_learning_restarts:          0
% 7.17/1.52  inst_num_moves_active_passive:          108
% 7.17/1.52  inst_lit_activity:                      0
% 7.17/1.52  inst_lit_activity_moves:                0
% 7.17/1.52  inst_num_tautologies:                   0
% 7.17/1.52  inst_num_prop_implied:                  0
% 7.17/1.52  inst_num_existing_simplified:           0
% 7.17/1.52  inst_num_eq_res_simplified:             0
% 7.17/1.52  inst_num_child_elim:                    0
% 7.17/1.52  inst_num_of_dismatching_blockings:      405
% 7.17/1.52  inst_num_of_non_proper_insts:           1527
% 7.17/1.52  inst_num_of_duplicates:                 0
% 7.17/1.52  inst_inst_num_from_inst_to_res:         0
% 7.17/1.52  inst_dismatching_checking_time:         0.
% 7.17/1.52  
% 7.17/1.52  ------ Resolution
% 7.17/1.52  
% 7.17/1.52  res_num_of_clauses:                     0
% 7.17/1.52  res_num_in_passive:                     0
% 7.17/1.52  res_num_in_active:                      0
% 7.17/1.52  res_num_of_loops:                       115
% 7.17/1.52  res_forward_subset_subsumed:            192
% 7.17/1.52  res_backward_subset_subsumed:           0
% 7.17/1.52  res_forward_subsumed:                   0
% 7.17/1.52  res_backward_subsumed:                  0
% 7.17/1.52  res_forward_subsumption_resolution:     0
% 7.17/1.52  res_backward_subsumption_resolution:    0
% 7.17/1.52  res_clause_to_clause_subsumption:       3270
% 7.17/1.52  res_orphan_elimination:                 0
% 7.17/1.52  res_tautology_del:                      197
% 7.17/1.52  res_num_eq_res_simplified:              0
% 7.17/1.52  res_num_sel_changes:                    0
% 7.17/1.52  res_moves_from_active_to_pass:          0
% 7.17/1.52  
% 7.17/1.52  ------ Superposition
% 7.17/1.52  
% 7.17/1.52  sup_time_total:                         0.
% 7.17/1.52  sup_time_generating:                    0.
% 7.17/1.52  sup_time_sim_full:                      0.
% 7.17/1.52  sup_time_sim_immed:                     0.
% 7.17/1.52  
% 7.17/1.52  sup_num_of_clauses:                     678
% 7.17/1.52  sup_num_in_active:                      201
% 7.17/1.52  sup_num_in_passive:                     477
% 7.17/1.52  sup_num_of_loops:                       206
% 7.17/1.52  sup_fw_superposition:                   382
% 7.17/1.52  sup_bw_superposition:                   449
% 7.17/1.52  sup_immediate_simplified:               111
% 7.17/1.52  sup_given_eliminated:                   0
% 7.17/1.52  comparisons_done:                       0
% 7.17/1.52  comparisons_avoided:                    66
% 7.17/1.52  
% 7.17/1.52  ------ Simplifications
% 7.17/1.52  
% 7.17/1.52  
% 7.17/1.52  sim_fw_subset_subsumed:                 74
% 7.17/1.52  sim_bw_subset_subsumed:                 6
% 7.17/1.52  sim_fw_subsumed:                        26
% 7.17/1.52  sim_bw_subsumed:                        0
% 7.17/1.52  sim_fw_subsumption_res:                 1
% 7.17/1.52  sim_bw_subsumption_res:                 0
% 7.17/1.52  sim_tautology_del:                      20
% 7.17/1.52  sim_eq_tautology_del:                   5
% 7.17/1.52  sim_eq_res_simp:                        0
% 7.17/1.52  sim_fw_demodulated:                     2
% 7.17/1.52  sim_bw_demodulated:                     3
% 7.17/1.52  sim_light_normalised:                   13
% 7.17/1.52  sim_joinable_taut:                      0
% 7.17/1.52  sim_joinable_simp:                      0
% 7.17/1.52  sim_ac_normalised:                      0
% 7.17/1.52  sim_smt_subsumption:                    0
% 7.17/1.52  
%------------------------------------------------------------------------------
