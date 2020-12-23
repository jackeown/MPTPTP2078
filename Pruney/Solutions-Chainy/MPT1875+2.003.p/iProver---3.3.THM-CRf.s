%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:41 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 412 expanded)
%              Number of clauses        :  112 ( 158 expanded)
%              Number of leaves         :   30 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  726 (1698 expanded)
%              Number of equality atoms :  164 ( 227 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f56])).

fof(f59,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v4_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v4_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v1_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f67,f66])).

fof(f103,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f68])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f99,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f101,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f22,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f61])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f94,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f86,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2826,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3395,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2826])).

cnf(c_19,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2820,plain,
    ( v2_tex_2(X0_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | r1_tarski(sK0(X0_53,X0_54),X0_54)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3401,plain,
    ( v2_tex_2(X0_54,X0_53) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | r1_tarski(sK0(X0_53,X0_54),X0_54) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2820])).

cnf(c_4394,plain,
    ( v2_tex_2(k1_xboole_0,X0_53) = iProver_top
    | r1_tarski(sK0(X0_53,k1_xboole_0),k1_xboole_0) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_3401])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2831,plain,
    ( ~ r1_tarski(X0_54,k1_xboole_0)
    | k1_xboole_0 = X0_54 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3391,plain,
    ( k1_xboole_0 = X0_54
    | r1_tarski(X0_54,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_7272,plain,
    ( sK0(X0_53,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4394,c_3391])).

cnf(c_7274,plain,
    ( sK0(sK3,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7272])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_385,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_386,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k1_xboole_0 = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_402,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9,c_386])).

cnf(c_2808,plain,
    ( ~ v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | u1_struct_0(X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_6188,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK3,sK4))
    | ~ l1_pre_topc(k1_pre_topc(sK3,sK4))
    | u1_struct_0(k1_pre_topc(sK3,sK4)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2808])).

cnf(c_2838,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3947,plain,
    ( X0_54 != X1_54
    | sK4 != X1_54
    | sK4 = X0_54 ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_6053,plain,
    ( X0_54 != u1_struct_0(k1_pre_topc(sK3,sK4))
    | sK4 = X0_54
    | sK4 != u1_struct_0(k1_pre_topc(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3947])).

cnf(c_6056,plain,
    ( sK4 != u1_struct_0(k1_pre_topc(sK3,sK4))
    | sK4 = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(k1_pre_topc(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6053])).

cnf(c_2851,plain,
    ( ~ v2_tex_2(X0_54,X0_53)
    | v2_tex_2(X1_54,X1_53)
    | X1_54 != X0_54
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3869,plain,
    ( ~ v2_tex_2(X0_54,X0_53)
    | v2_tex_2(sK4,sK3)
    | sK4 != X0_54
    | sK3 != X0_53 ),
    inference(instantiation,[status(thm)],[c_2851])).

cnf(c_6042,plain,
    ( ~ v2_tex_2(u1_struct_0(k1_pre_topc(sK3,sK4)),X0_53)
    | v2_tex_2(sK4,sK3)
    | sK4 != u1_struct_0(k1_pre_topc(sK3,sK4))
    | sK3 != X0_53 ),
    inference(instantiation,[status(thm)],[c_3869])).

cnf(c_6044,plain,
    ( ~ v2_tex_2(u1_struct_0(k1_pre_topc(sK3,sK4)),sK3)
    | v2_tex_2(sK4,sK3)
    | sK4 != u1_struct_0(k1_pre_topc(sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6042])).

cnf(c_5137,plain,
    ( X0_54 != X1_54
    | X0_54 = u1_struct_0(k1_pre_topc(sK3,sK4))
    | u1_struct_0(k1_pre_topc(sK3,sK4)) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_5138,plain,
    ( u1_struct_0(k1_pre_topc(sK3,sK4)) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK3,sK4))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5137])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2829,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X0_54,X2_54) = k9_subset_1(X1_54,X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3392,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k9_subset_1(X0_54,X2_54,X1_54)
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2829])).

cnf(c_3761,plain,
    ( k9_subset_1(X0_54,X1_54,k1_xboole_0) = k9_subset_1(X0_54,k1_xboole_0,X1_54) ),
    inference(superposition,[status(thm)],[c_3395,c_3392])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2814,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3407,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2827,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3394,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2827])).

cnf(c_4103,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0_54,sK4) = k1_setfam_1(k2_tarski(X0_54,sK4)) ),
    inference(superposition,[status(thm)],[c_3407,c_3394])).

cnf(c_3760,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0_54,sK4) = k9_subset_1(u1_struct_0(sK3),sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_3407,c_3392])).

cnf(c_4435,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,X0_54) = k1_setfam_1(k2_tarski(X0_54,sK4)) ),
    inference(demodulation,[status(thm)],[c_4103,c_3760])).

cnf(c_4719,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,sK4) = k1_setfam_1(k2_tarski(k1_xboole_0,sK4)) ),
    inference(superposition,[status(thm)],[c_3761,c_4435])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2832,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_54,X1_54)),X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3390,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_54,X1_54)),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2832])).

cnf(c_3845,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3390,c_3391])).

cnf(c_4721,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4719,c_3845,c_4103])).

cnf(c_18,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2821,plain,
    ( v2_tex_2(X0_54,X0_53)
    | ~ v4_pre_topc(X1_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | k9_subset_1(u1_struct_0(X0_53),X0_54,X1_54) != sK0(X0_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3400,plain,
    ( k9_subset_1(u1_struct_0(X0_53),X0_54,X1_54) != sK0(X0_53,X0_54)
    | v2_tex_2(X0_54,X0_53) = iProver_top
    | v4_pre_topc(X1_54,X0_53) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2821])).

cnf(c_4815,plain,
    ( sK0(sK3,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | v4_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4721,c_3400])).

cnf(c_4898,plain,
    ( v2_tex_2(k1_xboole_0,sK3)
    | ~ v4_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4815])).

cnf(c_4264,plain,
    ( X0_54 != sK4
    | sK4 = X0_54
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3947])).

cnf(c_4750,plain,
    ( u1_struct_0(k1_pre_topc(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(k1_pre_topc(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4264])).

cnf(c_8,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2825,plain,
    ( m1_pre_topc(k1_pre_topc(X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3396,plain,
    ( m1_pre_topc(k1_pre_topc(X0_53,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_4208,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3407,c_3396])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_38,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3683,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_3684,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3683])).

cnf(c_4535,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4208,c_38,c_39,c_3684])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2824,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3397,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_4541,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4535,c_3397])).

cnf(c_4549,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4541])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_633,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_634,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v1_tdlat_3(X0)
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_32,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_636,plain,
    ( v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_34,c_32,c_31])).

cnf(c_637,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v1_tdlat_3(X0) ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_2805,plain,
    ( ~ m1_pre_topc(X0_53,sK3)
    | v1_tdlat_3(X0_53) ),
    inference(subtyping,[status(esa)],[c_637])).

cnf(c_3950,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
    | v1_tdlat_3(k1_pre_topc(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_3870,plain,
    ( sK4 != X0_54
    | sK3 != X0_53
    | v2_tex_2(X0_54,X0_53) != iProver_top
    | v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3869])).

cnf(c_3872,plain,
    ( sK4 != k1_xboole_0
    | sK3 != sK3
    | v2_tex_2(sK4,sK3) = iProver_top
    | v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3870])).

cnf(c_3871,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v2_tex_2(k1_xboole_0,sK3)
    | sK4 != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3869])).

cnf(c_2835,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3805,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2835])).

cnf(c_27,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_192,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_15])).

cnf(c_193,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_2809,plain,
    ( v2_tex_2(u1_struct_0(X0_53),X1_53)
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ v1_tdlat_3(X0_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_3747,plain,
    ( v2_tex_2(u1_struct_0(k1_pre_topc(sK3,sK4)),sK3)
    | ~ m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
    | ~ v1_tdlat_3(k1_pre_topc(sK3,sK4))
    | v2_struct_0(k1_pre_topc(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2809])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2823,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53)
    | u1_struct_0(k1_pre_topc(X0_53,X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3676,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2823])).

cnf(c_3659,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_53))) ),
    inference(instantiation,[status(thm)],[c_2826])).

cnf(c_3663,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3659])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_441,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_tdlat_3(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_442,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_16,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_458,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_442,c_16,c_5])).

cnf(c_2807,plain,
    ( v4_pre_topc(X0_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ v1_tdlat_3(X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_3655,plain,
    ( v4_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2807])).

cnf(c_2866,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2835])).

cnf(c_2834,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2865,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_29,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_40,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7274,c_6188,c_6056,c_6044,c_5138,c_4898,c_4750,c_4549,c_3950,c_3872,c_3871,c_3805,c_3747,c_3683,c_3676,c_3663,c_3655,c_2866,c_2865,c_40,c_29,c_30,c_38,c_31,c_32,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:13:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.49/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/0.99  
% 2.49/0.99  ------  iProver source info
% 2.49/0.99  
% 2.49/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.49/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/0.99  git: non_committed_changes: false
% 2.49/0.99  git: last_make_outside_of_git: false
% 2.49/0.99  
% 2.49/0.99  ------ 
% 2.49/0.99  
% 2.49/0.99  ------ Input Options
% 2.49/0.99  
% 2.49/0.99  --out_options                           all
% 2.49/0.99  --tptp_safe_out                         true
% 2.49/0.99  --problem_path                          ""
% 2.49/0.99  --include_path                          ""
% 2.49/0.99  --clausifier                            res/vclausify_rel
% 2.49/0.99  --clausifier_options                    --mode clausify
% 2.49/0.99  --stdin                                 false
% 2.49/0.99  --stats_out                             all
% 2.49/0.99  
% 2.49/0.99  ------ General Options
% 2.49/0.99  
% 2.49/0.99  --fof                                   false
% 2.49/0.99  --time_out_real                         305.
% 2.49/0.99  --time_out_virtual                      -1.
% 2.49/0.99  --symbol_type_check                     false
% 2.49/0.99  --clausify_out                          false
% 2.49/0.99  --sig_cnt_out                           false
% 2.49/0.99  --trig_cnt_out                          false
% 2.49/0.99  --trig_cnt_out_tolerance                1.
% 2.49/0.99  --trig_cnt_out_sk_spl                   false
% 2.49/0.99  --abstr_cl_out                          false
% 2.49/0.99  
% 2.49/0.99  ------ Global Options
% 2.49/0.99  
% 2.49/0.99  --schedule                              default
% 2.49/0.99  --add_important_lit                     false
% 2.49/0.99  --prop_solver_per_cl                    1000
% 2.49/0.99  --min_unsat_core                        false
% 2.49/0.99  --soft_assumptions                      false
% 2.49/0.99  --soft_lemma_size                       3
% 2.49/0.99  --prop_impl_unit_size                   0
% 2.49/0.99  --prop_impl_unit                        []
% 2.49/0.99  --share_sel_clauses                     true
% 2.49/0.99  --reset_solvers                         false
% 2.49/0.99  --bc_imp_inh                            [conj_cone]
% 2.49/0.99  --conj_cone_tolerance                   3.
% 2.49/0.99  --extra_neg_conj                        none
% 2.49/0.99  --large_theory_mode                     true
% 2.49/0.99  --prolific_symb_bound                   200
% 2.49/0.99  --lt_threshold                          2000
% 2.49/0.99  --clause_weak_htbl                      true
% 2.49/0.99  --gc_record_bc_elim                     false
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing Options
% 2.49/0.99  
% 2.49/0.99  --preprocessing_flag                    true
% 2.49/0.99  --time_out_prep_mult                    0.1
% 2.49/0.99  --splitting_mode                        input
% 2.49/0.99  --splitting_grd                         true
% 2.49/0.99  --splitting_cvd                         false
% 2.49/0.99  --splitting_cvd_svl                     false
% 2.49/0.99  --splitting_nvd                         32
% 2.49/0.99  --sub_typing                            true
% 2.49/0.99  --prep_gs_sim                           true
% 2.49/0.99  --prep_unflatten                        true
% 2.49/0.99  --prep_res_sim                          true
% 2.49/0.99  --prep_upred                            true
% 2.49/0.99  --prep_sem_filter                       exhaustive
% 2.49/0.99  --prep_sem_filter_out                   false
% 2.49/0.99  --pred_elim                             true
% 2.49/0.99  --res_sim_input                         true
% 2.49/0.99  --eq_ax_congr_red                       true
% 2.49/0.99  --pure_diseq_elim                       true
% 2.49/0.99  --brand_transform                       false
% 2.49/0.99  --non_eq_to_eq                          false
% 2.49/0.99  --prep_def_merge                        true
% 2.49/0.99  --prep_def_merge_prop_impl              false
% 2.49/0.99  --prep_def_merge_mbd                    true
% 2.49/0.99  --prep_def_merge_tr_red                 false
% 2.49/0.99  --prep_def_merge_tr_cl                  false
% 2.49/0.99  --smt_preprocessing                     true
% 2.49/0.99  --smt_ac_axioms                         fast
% 2.49/0.99  --preprocessed_out                      false
% 2.49/0.99  --preprocessed_stats                    false
% 2.49/0.99  
% 2.49/0.99  ------ Abstraction refinement Options
% 2.49/0.99  
% 2.49/0.99  --abstr_ref                             []
% 2.49/0.99  --abstr_ref_prep                        false
% 2.49/0.99  --abstr_ref_until_sat                   false
% 2.49/0.99  --abstr_ref_sig_restrict                funpre
% 2.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.99  --abstr_ref_under                       []
% 2.49/0.99  
% 2.49/0.99  ------ SAT Options
% 2.49/0.99  
% 2.49/0.99  --sat_mode                              false
% 2.49/0.99  --sat_fm_restart_options                ""
% 2.49/0.99  --sat_gr_def                            false
% 2.49/0.99  --sat_epr_types                         true
% 2.49/0.99  --sat_non_cyclic_types                  false
% 2.49/0.99  --sat_finite_models                     false
% 2.49/0.99  --sat_fm_lemmas                         false
% 2.49/0.99  --sat_fm_prep                           false
% 2.49/0.99  --sat_fm_uc_incr                        true
% 2.49/0.99  --sat_out_model                         small
% 2.49/0.99  --sat_out_clauses                       false
% 2.49/0.99  
% 2.49/0.99  ------ QBF Options
% 2.49/0.99  
% 2.49/0.99  --qbf_mode                              false
% 2.49/0.99  --qbf_elim_univ                         false
% 2.49/0.99  --qbf_dom_inst                          none
% 2.49/0.99  --qbf_dom_pre_inst                      false
% 2.49/0.99  --qbf_sk_in                             false
% 2.49/0.99  --qbf_pred_elim                         true
% 2.49/0.99  --qbf_split                             512
% 2.49/0.99  
% 2.49/0.99  ------ BMC1 Options
% 2.49/0.99  
% 2.49/0.99  --bmc1_incremental                      false
% 2.49/0.99  --bmc1_axioms                           reachable_all
% 2.49/0.99  --bmc1_min_bound                        0
% 2.49/0.99  --bmc1_max_bound                        -1
% 2.49/0.99  --bmc1_max_bound_default                -1
% 2.49/0.99  --bmc1_symbol_reachability              true
% 2.49/0.99  --bmc1_property_lemmas                  false
% 2.49/0.99  --bmc1_k_induction                      false
% 2.49/0.99  --bmc1_non_equiv_states                 false
% 2.49/0.99  --bmc1_deadlock                         false
% 2.49/0.99  --bmc1_ucm                              false
% 2.49/0.99  --bmc1_add_unsat_core                   none
% 2.49/0.99  --bmc1_unsat_core_children              false
% 2.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.99  --bmc1_out_stat                         full
% 2.49/0.99  --bmc1_ground_init                      false
% 2.49/0.99  --bmc1_pre_inst_next_state              false
% 2.49/0.99  --bmc1_pre_inst_state                   false
% 2.49/0.99  --bmc1_pre_inst_reach_state             false
% 2.49/0.99  --bmc1_out_unsat_core                   false
% 2.49/0.99  --bmc1_aig_witness_out                  false
% 2.49/0.99  --bmc1_verbose                          false
% 2.49/0.99  --bmc1_dump_clauses_tptp                false
% 2.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.99  --bmc1_dump_file                        -
% 2.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.99  --bmc1_ucm_extend_mode                  1
% 2.49/0.99  --bmc1_ucm_init_mode                    2
% 2.49/0.99  --bmc1_ucm_cone_mode                    none
% 2.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.99  --bmc1_ucm_relax_model                  4
% 2.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.99  --bmc1_ucm_layered_model                none
% 2.49/0.99  --bmc1_ucm_max_lemma_size               10
% 2.49/0.99  
% 2.49/0.99  ------ AIG Options
% 2.49/0.99  
% 2.49/0.99  --aig_mode                              false
% 2.49/0.99  
% 2.49/0.99  ------ Instantiation Options
% 2.49/0.99  
% 2.49/0.99  --instantiation_flag                    true
% 2.49/0.99  --inst_sos_flag                         false
% 2.49/0.99  --inst_sos_phase                        true
% 2.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel_side                     num_symb
% 2.49/0.99  --inst_solver_per_active                1400
% 2.49/0.99  --inst_solver_calls_frac                1.
% 2.49/0.99  --inst_passive_queue_type               priority_queues
% 2.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.99  --inst_passive_queues_freq              [25;2]
% 2.49/0.99  --inst_dismatching                      true
% 2.49/0.99  --inst_eager_unprocessed_to_passive     true
% 2.49/0.99  --inst_prop_sim_given                   true
% 2.49/0.99  --inst_prop_sim_new                     false
% 2.49/0.99  --inst_subs_new                         false
% 2.49/0.99  --inst_eq_res_simp                      false
% 2.49/0.99  --inst_subs_given                       false
% 2.49/0.99  --inst_orphan_elimination               true
% 2.49/0.99  --inst_learning_loop_flag               true
% 2.49/0.99  --inst_learning_start                   3000
% 2.49/0.99  --inst_learning_factor                  2
% 2.49/0.99  --inst_start_prop_sim_after_learn       3
% 2.49/0.99  --inst_sel_renew                        solver
% 2.49/0.99  --inst_lit_activity_flag                true
% 2.49/0.99  --inst_restr_to_given                   false
% 2.49/0.99  --inst_activity_threshold               500
% 2.49/0.99  --inst_out_proof                        true
% 2.49/0.99  
% 2.49/0.99  ------ Resolution Options
% 2.49/0.99  
% 2.49/0.99  --resolution_flag                       true
% 2.49/0.99  --res_lit_sel                           adaptive
% 2.49/0.99  --res_lit_sel_side                      none
% 2.49/0.99  --res_ordering                          kbo
% 2.49/0.99  --res_to_prop_solver                    active
% 2.49/0.99  --res_prop_simpl_new                    false
% 2.49/0.99  --res_prop_simpl_given                  true
% 2.49/0.99  --res_passive_queue_type                priority_queues
% 2.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.99  --res_passive_queues_freq               [15;5]
% 2.49/0.99  --res_forward_subs                      full
% 2.49/0.99  --res_backward_subs                     full
% 2.49/0.99  --res_forward_subs_resolution           true
% 2.49/0.99  --res_backward_subs_resolution          true
% 2.49/0.99  --res_orphan_elimination                true
% 2.49/0.99  --res_time_limit                        2.
% 2.49/0.99  --res_out_proof                         true
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Options
% 2.49/0.99  
% 2.49/0.99  --superposition_flag                    true
% 2.49/0.99  --sup_passive_queue_type                priority_queues
% 2.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.99  --demod_completeness_check              fast
% 2.49/0.99  --demod_use_ground                      true
% 2.49/0.99  --sup_to_prop_solver                    passive
% 2.49/0.99  --sup_prop_simpl_new                    true
% 2.49/0.99  --sup_prop_simpl_given                  true
% 2.49/0.99  --sup_fun_splitting                     false
% 2.49/0.99  --sup_smt_interval                      50000
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Simplification Setup
% 2.49/0.99  
% 2.49/0.99  --sup_indices_passive                   []
% 2.49/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_full_bw                           [BwDemod]
% 2.49/0.99  --sup_immed_triv                        [TrivRules]
% 2.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_immed_bw_main                     []
% 2.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  
% 2.49/0.99  ------ Combination Options
% 2.49/0.99  
% 2.49/0.99  --comb_res_mult                         3
% 2.49/0.99  --comb_sup_mult                         2
% 2.49/0.99  --comb_inst_mult                        10
% 2.49/0.99  
% 2.49/0.99  ------ Debug Options
% 2.49/0.99  
% 2.49/0.99  --dbg_backtrace                         false
% 2.49/0.99  --dbg_dump_prop_clauses                 false
% 2.49/0.99  --dbg_dump_prop_clauses_file            -
% 2.49/0.99  --dbg_out_stat                          false
% 2.49/0.99  ------ Parsing...
% 2.49/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/0.99  ------ Proving...
% 2.49/0.99  ------ Problem Properties 
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  clauses                                 28
% 2.49/0.99  conjectures                             5
% 2.49/0.99  EPR                                     8
% 2.49/0.99  Horn                                    23
% 2.49/0.99  unary                                   8
% 2.49/0.99  binary                                  5
% 2.49/0.99  lits                                    86
% 2.49/0.99  lits eq                                 8
% 2.49/0.99  fd_pure                                 0
% 2.49/0.99  fd_pseudo                               0
% 2.49/0.99  fd_cond                                 1
% 2.49/0.99  fd_pseudo_cond                          0
% 2.49/0.99  AC symbols                              0
% 2.49/0.99  
% 2.49/0.99  ------ Schedule dynamic 5 is on 
% 2.49/0.99  
% 2.49/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  ------ 
% 2.49/0.99  Current options:
% 2.49/0.99  ------ 
% 2.49/0.99  
% 2.49/0.99  ------ Input Options
% 2.49/0.99  
% 2.49/0.99  --out_options                           all
% 2.49/0.99  --tptp_safe_out                         true
% 2.49/0.99  --problem_path                          ""
% 2.49/0.99  --include_path                          ""
% 2.49/0.99  --clausifier                            res/vclausify_rel
% 2.49/0.99  --clausifier_options                    --mode clausify
% 2.49/0.99  --stdin                                 false
% 2.49/0.99  --stats_out                             all
% 2.49/0.99  
% 2.49/0.99  ------ General Options
% 2.49/0.99  
% 2.49/0.99  --fof                                   false
% 2.49/0.99  --time_out_real                         305.
% 2.49/0.99  --time_out_virtual                      -1.
% 2.49/0.99  --symbol_type_check                     false
% 2.49/0.99  --clausify_out                          false
% 2.49/0.99  --sig_cnt_out                           false
% 2.49/0.99  --trig_cnt_out                          false
% 2.49/0.99  --trig_cnt_out_tolerance                1.
% 2.49/0.99  --trig_cnt_out_sk_spl                   false
% 2.49/0.99  --abstr_cl_out                          false
% 2.49/0.99  
% 2.49/0.99  ------ Global Options
% 2.49/0.99  
% 2.49/0.99  --schedule                              default
% 2.49/0.99  --add_important_lit                     false
% 2.49/0.99  --prop_solver_per_cl                    1000
% 2.49/0.99  --min_unsat_core                        false
% 2.49/0.99  --soft_assumptions                      false
% 2.49/0.99  --soft_lemma_size                       3
% 2.49/0.99  --prop_impl_unit_size                   0
% 2.49/0.99  --prop_impl_unit                        []
% 2.49/0.99  --share_sel_clauses                     true
% 2.49/0.99  --reset_solvers                         false
% 2.49/0.99  --bc_imp_inh                            [conj_cone]
% 2.49/0.99  --conj_cone_tolerance                   3.
% 2.49/0.99  --extra_neg_conj                        none
% 2.49/0.99  --large_theory_mode                     true
% 2.49/0.99  --prolific_symb_bound                   200
% 2.49/0.99  --lt_threshold                          2000
% 2.49/0.99  --clause_weak_htbl                      true
% 2.49/0.99  --gc_record_bc_elim                     false
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing Options
% 2.49/0.99  
% 2.49/0.99  --preprocessing_flag                    true
% 2.49/0.99  --time_out_prep_mult                    0.1
% 2.49/0.99  --splitting_mode                        input
% 2.49/0.99  --splitting_grd                         true
% 2.49/0.99  --splitting_cvd                         false
% 2.49/0.99  --splitting_cvd_svl                     false
% 2.49/0.99  --splitting_nvd                         32
% 2.49/0.99  --sub_typing                            true
% 2.49/0.99  --prep_gs_sim                           true
% 2.49/0.99  --prep_unflatten                        true
% 2.49/0.99  --prep_res_sim                          true
% 2.49/0.99  --prep_upred                            true
% 2.49/0.99  --prep_sem_filter                       exhaustive
% 2.49/0.99  --prep_sem_filter_out                   false
% 2.49/0.99  --pred_elim                             true
% 2.49/0.99  --res_sim_input                         true
% 2.49/0.99  --eq_ax_congr_red                       true
% 2.49/0.99  --pure_diseq_elim                       true
% 2.49/0.99  --brand_transform                       false
% 2.49/0.99  --non_eq_to_eq                          false
% 2.49/0.99  --prep_def_merge                        true
% 2.49/0.99  --prep_def_merge_prop_impl              false
% 2.49/0.99  --prep_def_merge_mbd                    true
% 2.49/0.99  --prep_def_merge_tr_red                 false
% 2.49/0.99  --prep_def_merge_tr_cl                  false
% 2.49/0.99  --smt_preprocessing                     true
% 2.49/0.99  --smt_ac_axioms                         fast
% 2.49/0.99  --preprocessed_out                      false
% 2.49/0.99  --preprocessed_stats                    false
% 2.49/0.99  
% 2.49/0.99  ------ Abstraction refinement Options
% 2.49/0.99  
% 2.49/0.99  --abstr_ref                             []
% 2.49/0.99  --abstr_ref_prep                        false
% 2.49/0.99  --abstr_ref_until_sat                   false
% 2.49/0.99  --abstr_ref_sig_restrict                funpre
% 2.49/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.99  --abstr_ref_under                       []
% 2.49/0.99  
% 2.49/0.99  ------ SAT Options
% 2.49/0.99  
% 2.49/0.99  --sat_mode                              false
% 2.49/0.99  --sat_fm_restart_options                ""
% 2.49/0.99  --sat_gr_def                            false
% 2.49/0.99  --sat_epr_types                         true
% 2.49/0.99  --sat_non_cyclic_types                  false
% 2.49/0.99  --sat_finite_models                     false
% 2.49/0.99  --sat_fm_lemmas                         false
% 2.49/0.99  --sat_fm_prep                           false
% 2.49/0.99  --sat_fm_uc_incr                        true
% 2.49/0.99  --sat_out_model                         small
% 2.49/0.99  --sat_out_clauses                       false
% 2.49/0.99  
% 2.49/0.99  ------ QBF Options
% 2.49/0.99  
% 2.49/0.99  --qbf_mode                              false
% 2.49/0.99  --qbf_elim_univ                         false
% 2.49/0.99  --qbf_dom_inst                          none
% 2.49/0.99  --qbf_dom_pre_inst                      false
% 2.49/0.99  --qbf_sk_in                             false
% 2.49/0.99  --qbf_pred_elim                         true
% 2.49/0.99  --qbf_split                             512
% 2.49/0.99  
% 2.49/0.99  ------ BMC1 Options
% 2.49/0.99  
% 2.49/0.99  --bmc1_incremental                      false
% 2.49/0.99  --bmc1_axioms                           reachable_all
% 2.49/0.99  --bmc1_min_bound                        0
% 2.49/0.99  --bmc1_max_bound                        -1
% 2.49/0.99  --bmc1_max_bound_default                -1
% 2.49/0.99  --bmc1_symbol_reachability              true
% 2.49/0.99  --bmc1_property_lemmas                  false
% 2.49/0.99  --bmc1_k_induction                      false
% 2.49/0.99  --bmc1_non_equiv_states                 false
% 2.49/0.99  --bmc1_deadlock                         false
% 2.49/0.99  --bmc1_ucm                              false
% 2.49/0.99  --bmc1_add_unsat_core                   none
% 2.49/0.99  --bmc1_unsat_core_children              false
% 2.49/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.99  --bmc1_out_stat                         full
% 2.49/0.99  --bmc1_ground_init                      false
% 2.49/0.99  --bmc1_pre_inst_next_state              false
% 2.49/0.99  --bmc1_pre_inst_state                   false
% 2.49/0.99  --bmc1_pre_inst_reach_state             false
% 2.49/0.99  --bmc1_out_unsat_core                   false
% 2.49/0.99  --bmc1_aig_witness_out                  false
% 2.49/0.99  --bmc1_verbose                          false
% 2.49/0.99  --bmc1_dump_clauses_tptp                false
% 2.49/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.99  --bmc1_dump_file                        -
% 2.49/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.99  --bmc1_ucm_extend_mode                  1
% 2.49/0.99  --bmc1_ucm_init_mode                    2
% 2.49/0.99  --bmc1_ucm_cone_mode                    none
% 2.49/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.99  --bmc1_ucm_relax_model                  4
% 2.49/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.99  --bmc1_ucm_layered_model                none
% 2.49/0.99  --bmc1_ucm_max_lemma_size               10
% 2.49/0.99  
% 2.49/0.99  ------ AIG Options
% 2.49/0.99  
% 2.49/0.99  --aig_mode                              false
% 2.49/0.99  
% 2.49/0.99  ------ Instantiation Options
% 2.49/0.99  
% 2.49/0.99  --instantiation_flag                    true
% 2.49/0.99  --inst_sos_flag                         false
% 2.49/0.99  --inst_sos_phase                        true
% 2.49/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.99  --inst_lit_sel_side                     none
% 2.49/0.99  --inst_solver_per_active                1400
% 2.49/0.99  --inst_solver_calls_frac                1.
% 2.49/0.99  --inst_passive_queue_type               priority_queues
% 2.49/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.99  --inst_passive_queues_freq              [25;2]
% 2.49/0.99  --inst_dismatching                      true
% 2.49/0.99  --inst_eager_unprocessed_to_passive     true
% 2.49/0.99  --inst_prop_sim_given                   true
% 2.49/0.99  --inst_prop_sim_new                     false
% 2.49/0.99  --inst_subs_new                         false
% 2.49/0.99  --inst_eq_res_simp                      false
% 2.49/0.99  --inst_subs_given                       false
% 2.49/0.99  --inst_orphan_elimination               true
% 2.49/0.99  --inst_learning_loop_flag               true
% 2.49/0.99  --inst_learning_start                   3000
% 2.49/0.99  --inst_learning_factor                  2
% 2.49/0.99  --inst_start_prop_sim_after_learn       3
% 2.49/0.99  --inst_sel_renew                        solver
% 2.49/0.99  --inst_lit_activity_flag                true
% 2.49/0.99  --inst_restr_to_given                   false
% 2.49/0.99  --inst_activity_threshold               500
% 2.49/0.99  --inst_out_proof                        true
% 2.49/0.99  
% 2.49/0.99  ------ Resolution Options
% 2.49/0.99  
% 2.49/0.99  --resolution_flag                       false
% 2.49/0.99  --res_lit_sel                           adaptive
% 2.49/0.99  --res_lit_sel_side                      none
% 2.49/0.99  --res_ordering                          kbo
% 2.49/0.99  --res_to_prop_solver                    active
% 2.49/0.99  --res_prop_simpl_new                    false
% 2.49/0.99  --res_prop_simpl_given                  true
% 2.49/0.99  --res_passive_queue_type                priority_queues
% 2.49/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.99  --res_passive_queues_freq               [15;5]
% 2.49/0.99  --res_forward_subs                      full
% 2.49/0.99  --res_backward_subs                     full
% 2.49/0.99  --res_forward_subs_resolution           true
% 2.49/0.99  --res_backward_subs_resolution          true
% 2.49/0.99  --res_orphan_elimination                true
% 2.49/0.99  --res_time_limit                        2.
% 2.49/0.99  --res_out_proof                         true
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Options
% 2.49/0.99  
% 2.49/0.99  --superposition_flag                    true
% 2.49/0.99  --sup_passive_queue_type                priority_queues
% 2.49/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.99  --demod_completeness_check              fast
% 2.49/0.99  --demod_use_ground                      true
% 2.49/0.99  --sup_to_prop_solver                    passive
% 2.49/0.99  --sup_prop_simpl_new                    true
% 2.49/0.99  --sup_prop_simpl_given                  true
% 2.49/0.99  --sup_fun_splitting                     false
% 2.49/0.99  --sup_smt_interval                      50000
% 2.49/0.99  
% 2.49/0.99  ------ Superposition Simplification Setup
% 2.49/0.99  
% 2.49/0.99  --sup_indices_passive                   []
% 2.49/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_full_bw                           [BwDemod]
% 2.49/0.99  --sup_immed_triv                        [TrivRules]
% 2.49/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_immed_bw_main                     []
% 2.49/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.99  
% 2.49/0.99  ------ Combination Options
% 2.49/0.99  
% 2.49/0.99  --comb_res_mult                         3
% 2.49/0.99  --comb_sup_mult                         2
% 2.49/0.99  --comb_inst_mult                        10
% 2.49/0.99  
% 2.49/0.99  ------ Debug Options
% 2.49/0.99  
% 2.49/0.99  --dbg_backtrace                         false
% 2.49/0.99  --dbg_dump_prop_clauses                 false
% 2.49/0.99  --dbg_dump_prop_clauses_file            -
% 2.49/0.99  --dbg_out_stat                          false
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  ------ Proving...
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  % SZS status Theorem for theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  fof(f8,axiom,(
% 2.49/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f76,plain,(
% 2.49/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f8])).
% 2.49/0.99  
% 2.49/0.99  fof(f20,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f47,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f20])).
% 2.49/0.99  
% 2.49/0.99  fof(f48,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f47])).
% 2.49/0.99  
% 2.49/0.99  fof(f56,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f48])).
% 2.49/0.99  
% 2.49/0.99  fof(f57,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(rectify,[],[f56])).
% 2.49/0.99  
% 2.49/0.99  fof(f59,plain,(
% 2.49/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f58,plain,(
% 2.49/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f60,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 2.49/0.99  
% 2.49/0.99  fof(f92,plain,(
% 2.49/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f60])).
% 2.49/0.99  
% 2.49/0.99  fof(f3,axiom,(
% 2.49/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f30,plain,(
% 2.49/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.49/0.99    inference(ennf_transformation,[],[f3])).
% 2.49/0.99  
% 2.49/0.99  fof(f71,plain,(
% 2.49/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f30])).
% 2.49/0.99  
% 2.49/0.99  fof(f12,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f36,plain,(
% 2.49/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f12])).
% 2.49/0.99  
% 2.49/0.99  fof(f79,plain,(
% 2.49/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f36])).
% 2.49/0.99  
% 2.49/0.99  fof(f1,axiom,(
% 2.49/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f29,plain,(
% 2.49/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f1])).
% 2.49/0.99  
% 2.49/0.99  fof(f69,plain,(
% 2.49/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f29])).
% 2.49/0.99  
% 2.49/0.99  fof(f14,axiom,(
% 2.49/0.99    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f38,plain,(
% 2.49/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f14])).
% 2.49/0.99  
% 2.49/0.99  fof(f39,plain,(
% 2.49/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 2.49/0.99    inference(flattening,[],[f38])).
% 2.49/0.99  
% 2.49/0.99  fof(f81,plain,(
% 2.49/0.99    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f39])).
% 2.49/0.99  
% 2.49/0.99  fof(f5,axiom,(
% 2.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f31,plain,(
% 2.49/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f5])).
% 2.49/0.99  
% 2.49/0.99  fof(f73,plain,(
% 2.49/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f31])).
% 2.49/0.99  
% 2.49/0.99  fof(f23,conjecture,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f24,negated_conjecture,(
% 2.49/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.49/0.99    inference(negated_conjecture,[],[f23])).
% 2.49/0.99  
% 2.49/0.99  fof(f53,plain,(
% 2.49/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f24])).
% 2.49/0.99  
% 2.49/0.99  fof(f54,plain,(
% 2.49/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.49/0.99    inference(flattening,[],[f53])).
% 2.49/0.99  
% 2.49/0.99  fof(f67,plain,(
% 2.49/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f66,plain,(
% 2.49/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f68,plain,(
% 2.49/0.99    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f67,f66])).
% 2.49/0.99  
% 2.49/0.99  fof(f103,plain,(
% 2.49/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.49/0.99    inference(cnf_transformation,[],[f68])).
% 2.49/0.99  
% 2.49/0.99  fof(f7,axiom,(
% 2.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f33,plain,(
% 2.49/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f7])).
% 2.49/0.99  
% 2.49/0.99  fof(f75,plain,(
% 2.49/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f33])).
% 2.49/0.99  
% 2.49/0.99  fof(f9,axiom,(
% 2.49/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f77,plain,(
% 2.49/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f9])).
% 2.49/0.99  
% 2.49/0.99  fof(f106,plain,(
% 2.49/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.49/0.99    inference(definition_unfolding,[],[f75,f77])).
% 2.49/0.99  
% 2.49/0.99  fof(f2,axiom,(
% 2.49/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f70,plain,(
% 2.49/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f2])).
% 2.49/0.99  
% 2.49/0.99  fof(f105,plain,(
% 2.49/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 2.49/0.99    inference(definition_unfolding,[],[f70,f77])).
% 2.49/0.99  
% 2.49/0.99  fof(f93,plain,(
% 2.49/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f60])).
% 2.49/0.99  
% 2.49/0.99  fof(f11,axiom,(
% 2.49/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f27,plain,(
% 2.49/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 2.49/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.49/0.99  
% 2.49/0.99  fof(f34,plain,(
% 2.49/0.99    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f27])).
% 2.49/0.99  
% 2.49/0.99  fof(f35,plain,(
% 2.49/0.99    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f34])).
% 2.49/0.99  
% 2.49/0.99  fof(f78,plain,(
% 2.49/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f35])).
% 2.49/0.99  
% 2.49/0.99  fof(f102,plain,(
% 2.49/0.99    l1_pre_topc(sK3)),
% 2.49/0.99    inference(cnf_transformation,[],[f68])).
% 2.49/0.99  
% 2.49/0.99  fof(f13,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f37,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f13])).
% 2.49/0.99  
% 2.49/0.99  fof(f80,plain,(
% 2.49/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f37])).
% 2.49/0.99  
% 2.49/0.99  fof(f19,axiom,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f25,plain,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 2.49/0.99    inference(pure_predicate_removal,[],[f19])).
% 2.49/0.99  
% 2.49/0.99  fof(f26,plain,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 2.49/0.99    inference(pure_predicate_removal,[],[f25])).
% 2.49/0.99  
% 2.49/0.99  fof(f45,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f26])).
% 2.49/0.99  
% 2.49/0.99  fof(f46,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/0.99    inference(flattening,[],[f45])).
% 2.49/0.99  
% 2.49/0.99  fof(f87,plain,(
% 2.49/0.99    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f46])).
% 2.49/0.99  
% 2.49/0.99  fof(f100,plain,(
% 2.49/0.99    v2_pre_topc(sK3)),
% 2.49/0.99    inference(cnf_transformation,[],[f68])).
% 2.49/0.99  
% 2.49/0.99  fof(f99,plain,(
% 2.49/0.99    ~v2_struct_0(sK3)),
% 2.49/0.99    inference(cnf_transformation,[],[f68])).
% 2.49/0.99  
% 2.49/0.99  fof(f101,plain,(
% 2.49/0.99    v1_tdlat_3(sK3)),
% 2.49/0.99    inference(cnf_transformation,[],[f68])).
% 2.49/0.99  
% 2.49/0.99  fof(f22,axiom,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f51,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f22])).
% 2.49/0.99  
% 2.49/0.99  fof(f52,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/0.99    inference(flattening,[],[f51])).
% 2.49/0.99  
% 2.49/0.99  fof(f65,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f52])).
% 2.49/0.99  
% 2.49/0.99  fof(f98,plain,(
% 2.49/0.99    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f65])).
% 2.49/0.99  
% 2.49/0.99  fof(f107,plain,(
% 2.49/0.99    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/0.99    inference(equality_resolution,[],[f98])).
% 2.49/0.99  
% 2.49/0.99  fof(f17,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f42,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f17])).
% 2.49/0.99  
% 2.49/0.99  fof(f85,plain,(
% 2.49/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f42])).
% 2.49/0.99  
% 2.49/0.99  fof(f15,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f40,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f15])).
% 2.49/0.99  
% 2.49/0.99  fof(f82,plain,(
% 2.49/0.99    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f40])).
% 2.49/0.99  
% 2.49/0.99  fof(f16,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f41,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f16])).
% 2.49/0.99  
% 2.49/0.99  fof(f55,plain,(
% 2.49/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f41])).
% 2.49/0.99  
% 2.49/0.99  fof(f84,plain,(
% 2.49/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f55])).
% 2.49/0.99  
% 2.49/0.99  fof(f21,axiom,(
% 2.49/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f49,plain,(
% 2.49/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f21])).
% 2.49/0.99  
% 2.49/0.99  fof(f50,plain,(
% 2.49/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f49])).
% 2.49/0.99  
% 2.49/0.99  fof(f61,plain,(
% 2.49/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.99    inference(nnf_transformation,[],[f50])).
% 2.49/0.99  
% 2.49/0.99  fof(f62,plain,(
% 2.49/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.99    inference(rectify,[],[f61])).
% 2.49/0.99  
% 2.49/0.99  fof(f63,plain,(
% 2.49/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/0.99    introduced(choice_axiom,[])).
% 2.49/0.99  
% 2.49/0.99  fof(f64,plain,(
% 2.49/0.99    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 2.49/0.99  
% 2.49/0.99  fof(f94,plain,(
% 2.49/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f64])).
% 2.49/0.99  
% 2.49/0.99  fof(f18,axiom,(
% 2.49/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f43,plain,(
% 2.49/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(ennf_transformation,[],[f18])).
% 2.49/0.99  
% 2.49/0.99  fof(f44,plain,(
% 2.49/0.99    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.49/0.99    inference(flattening,[],[f43])).
% 2.49/0.99  
% 2.49/0.99  fof(f86,plain,(
% 2.49/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.49/0.99    inference(cnf_transformation,[],[f44])).
% 2.49/0.99  
% 2.49/0.99  fof(f6,axiom,(
% 2.49/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.49/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.99  
% 2.49/0.99  fof(f32,plain,(
% 2.49/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.99    inference(ennf_transformation,[],[f6])).
% 2.49/0.99  
% 2.49/0.99  fof(f74,plain,(
% 2.49/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.49/0.99    inference(cnf_transformation,[],[f32])).
% 2.49/0.99  
% 2.49/0.99  fof(f104,plain,(
% 2.49/0.99    ~v2_tex_2(sK4,sK3)),
% 2.49/0.99    inference(cnf_transformation,[],[f68])).
% 2.49/0.99  
% 2.49/0.99  cnf(c_7,plain,
% 2.49/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.49/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2826,plain,
% 2.49/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3395,plain,
% 2.49/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2826]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_19,plain,
% 2.49/0.99      ( v2_tex_2(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | r1_tarski(sK0(X1,X0),X0)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2820,plain,
% 2.49/0.99      ( v2_tex_2(X0_54,X0_53)
% 2.49/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/0.99      | r1_tarski(sK0(X0_53,X0_54),X0_54)
% 2.49/0.99      | ~ l1_pre_topc(X0_53) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3401,plain,
% 2.49/0.99      ( v2_tex_2(X0_54,X0_53) = iProver_top
% 2.49/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/0.99      | r1_tarski(sK0(X0_53,X0_54),X0_54) = iProver_top
% 2.49/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2820]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4394,plain,
% 2.49/0.99      ( v2_tex_2(k1_xboole_0,X0_53) = iProver_top
% 2.49/0.99      | r1_tarski(sK0(X0_53,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.49/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3395,c_3401]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2,plain,
% 2.49/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.49/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2831,plain,
% 2.49/0.99      ( ~ r1_tarski(X0_54,k1_xboole_0) | k1_xboole_0 = X0_54 ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3391,plain,
% 2.49/0.99      ( k1_xboole_0 = X0_54
% 2.49/0.99      | r1_tarski(X0_54,k1_xboole_0) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_7272,plain,
% 2.49/0.99      ( sK0(X0_53,k1_xboole_0) = k1_xboole_0
% 2.49/0.99      | v2_tex_2(k1_xboole_0,X0_53) = iProver_top
% 2.49/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_4394,c_3391]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_7274,plain,
% 2.49/0.99      ( sK0(sK3,k1_xboole_0) = k1_xboole_0
% 2.49/0.99      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.49/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_7272]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_9,plain,
% 2.49/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_0,plain,
% 2.49/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.49/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_11,plain,
% 2.49/0.99      ( ~ v2_struct_0(X0)
% 2.49/0.99      | ~ l1_struct_0(X0)
% 2.49/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 2.49/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_385,plain,
% 2.49/0.99      ( ~ v2_struct_0(X0)
% 2.49/0.99      | ~ l1_struct_0(X0)
% 2.49/0.99      | u1_struct_0(X0) != X1
% 2.49/0.99      | k1_xboole_0 = X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_386,plain,
% 2.49/0.99      ( ~ v2_struct_0(X0)
% 2.49/0.99      | ~ l1_struct_0(X0)
% 2.49/0.99      | k1_xboole_0 = u1_struct_0(X0) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_402,plain,
% 2.49/0.99      ( ~ v2_struct_0(X0)
% 2.49/0.99      | ~ l1_pre_topc(X0)
% 2.49/0.99      | u1_struct_0(X0) = k1_xboole_0 ),
% 2.49/0.99      inference(resolution,[status(thm)],[c_9,c_386]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2808,plain,
% 2.49/0.99      ( ~ v2_struct_0(X0_53)
% 2.49/0.99      | ~ l1_pre_topc(X0_53)
% 2.49/0.99      | u1_struct_0(X0_53) = k1_xboole_0 ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_402]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6188,plain,
% 2.49/0.99      ( ~ v2_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | ~ l1_pre_topc(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | u1_struct_0(k1_pre_topc(sK3,sK4)) = k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2808]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2838,plain,
% 2.49/0.99      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.49/0.99      theory(equality) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3947,plain,
% 2.49/0.99      ( X0_54 != X1_54 | sK4 != X1_54 | sK4 = X0_54 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2838]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6053,plain,
% 2.49/0.99      ( X0_54 != u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | sK4 = X0_54
% 2.49/0.99      | sK4 != u1_struct_0(k1_pre_topc(sK3,sK4)) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_3947]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6056,plain,
% 2.49/0.99      ( sK4 != u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | sK4 = k1_xboole_0
% 2.49/0.99      | k1_xboole_0 != u1_struct_0(k1_pre_topc(sK3,sK4)) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_6053]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2851,plain,
% 2.49/0.99      ( ~ v2_tex_2(X0_54,X0_53)
% 2.49/0.99      | v2_tex_2(X1_54,X1_53)
% 2.49/0.99      | X1_54 != X0_54
% 2.49/0.99      | X1_53 != X0_53 ),
% 2.49/0.99      theory(equality) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3869,plain,
% 2.49/0.99      ( ~ v2_tex_2(X0_54,X0_53)
% 2.49/0.99      | v2_tex_2(sK4,sK3)
% 2.49/0.99      | sK4 != X0_54
% 2.49/0.99      | sK3 != X0_53 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2851]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6042,plain,
% 2.49/0.99      ( ~ v2_tex_2(u1_struct_0(k1_pre_topc(sK3,sK4)),X0_53)
% 2.49/0.99      | v2_tex_2(sK4,sK3)
% 2.49/0.99      | sK4 != u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | sK3 != X0_53 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_3869]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6044,plain,
% 2.49/0.99      ( ~ v2_tex_2(u1_struct_0(k1_pre_topc(sK3,sK4)),sK3)
% 2.49/0.99      | v2_tex_2(sK4,sK3)
% 2.49/0.99      | sK4 != u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | sK3 != sK3 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_6042]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_5137,plain,
% 2.49/0.99      ( X0_54 != X1_54
% 2.49/0.99      | X0_54 = u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | u1_struct_0(k1_pre_topc(sK3,sK4)) != X1_54 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2838]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_5138,plain,
% 2.49/0.99      ( u1_struct_0(k1_pre_topc(sK3,sK4)) != k1_xboole_0
% 2.49/0.99      | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_5137]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.49/0.99      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2829,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.49/0.99      | k9_subset_1(X1_54,X0_54,X2_54) = k9_subset_1(X1_54,X2_54,X0_54) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3392,plain,
% 2.49/0.99      ( k9_subset_1(X0_54,X1_54,X2_54) = k9_subset_1(X0_54,X2_54,X1_54)
% 2.49/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2829]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3761,plain,
% 2.49/0.99      ( k9_subset_1(X0_54,X1_54,k1_xboole_0) = k9_subset_1(X0_54,k1_xboole_0,X1_54) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3395,c_3392]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_30,negated_conjecture,
% 2.49/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2814,negated_conjecture,
% 2.49/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3407,plain,
% 2.49/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_6,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.49/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.49/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2827,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.49/0.99      | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3394,plain,
% 2.49/0.99      ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
% 2.49/0.99      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2827]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4103,plain,
% 2.49/0.99      ( k9_subset_1(u1_struct_0(sK3),X0_54,sK4) = k1_setfam_1(k2_tarski(X0_54,sK4)) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3407,c_3394]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3760,plain,
% 2.49/0.99      ( k9_subset_1(u1_struct_0(sK3),X0_54,sK4) = k9_subset_1(u1_struct_0(sK3),sK4,X0_54) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3407,c_3392]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4435,plain,
% 2.49/0.99      ( k9_subset_1(u1_struct_0(sK3),sK4,X0_54) = k1_setfam_1(k2_tarski(X0_54,sK4)) ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_4103,c_3760]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4719,plain,
% 2.49/0.99      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,sK4) = k1_setfam_1(k2_tarski(k1_xboole_0,sK4)) ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3761,c_4435]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_1,plain,
% 2.49/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2832,plain,
% 2.49/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0_54,X1_54)),X0_54) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3390,plain,
% 2.49/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0_54,X1_54)),X0_54) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2832]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3845,plain,
% 2.49/0.99      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_54)) = k1_xboole_0 ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3390,c_3391]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4721,plain,
% 2.49/0.99      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.49/0.99      inference(demodulation,[status(thm)],[c_4719,c_3845,c_4103]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_18,plain,
% 2.49/0.99      ( v2_tex_2(X0,X1)
% 2.49/0.99      | ~ v4_pre_topc(X2,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2821,plain,
% 2.49/0.99      ( v2_tex_2(X0_54,X0_53)
% 2.49/0.99      | ~ v4_pre_topc(X1_54,X0_53)
% 2.49/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/0.99      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/0.99      | ~ l1_pre_topc(X0_53)
% 2.49/0.99      | k9_subset_1(u1_struct_0(X0_53),X0_54,X1_54) != sK0(X0_53,X0_54) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3400,plain,
% 2.49/0.99      ( k9_subset_1(u1_struct_0(X0_53),X0_54,X1_54) != sK0(X0_53,X0_54)
% 2.49/0.99      | v2_tex_2(X0_54,X0_53) = iProver_top
% 2.49/0.99      | v4_pre_topc(X1_54,X0_53) != iProver_top
% 2.49/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2821]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4815,plain,
% 2.49/0.99      ( sK0(sK3,k1_xboole_0) != k1_xboole_0
% 2.49/0.99      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.49/0.99      | v4_pre_topc(sK4,sK3) != iProver_top
% 2.49/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_4721,c_3400]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4898,plain,
% 2.49/0.99      ( v2_tex_2(k1_xboole_0,sK3)
% 2.49/0.99      | ~ v4_pre_topc(sK4,sK3)
% 2.49/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/0.99      | ~ l1_pre_topc(sK3)
% 2.49/0.99      | sK0(sK3,k1_xboole_0) != k1_xboole_0 ),
% 2.49/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4815]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4264,plain,
% 2.49/0.99      ( X0_54 != sK4 | sK4 = X0_54 | sK4 != sK4 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_3947]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4750,plain,
% 2.49/0.99      ( u1_struct_0(k1_pre_topc(sK3,sK4)) != sK4
% 2.49/0.99      | sK4 = u1_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | sK4 != sK4 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_4264]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_8,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 2.49/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/0.99      | ~ l1_pre_topc(X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2825,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(X0_53,X0_54),X0_53)
% 2.49/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/0.99      | ~ l1_pre_topc(X0_53) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3396,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(X0_53,X0_54),X0_53) = iProver_top
% 2.49/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 2.49/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4208,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
% 2.49/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_3407,c_3396]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_31,negated_conjecture,
% 2.49/0.99      ( l1_pre_topc(sK3) ),
% 2.49/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_38,plain,
% 2.49/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_39,plain,
% 2.49/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3683,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
% 2.49/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/0.99      | ~ l1_pre_topc(sK3) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2825]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3684,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top
% 2.49/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.49/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_3683]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4535,plain,
% 2.49/0.99      ( m1_pre_topc(k1_pre_topc(sK3,sK4),sK3) = iProver_top ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_4208,c_38,c_39,c_3684]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_10,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2824,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.49/0.99      | ~ l1_pre_topc(X1_53)
% 2.49/0.99      | l1_pre_topc(X0_53) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3397,plain,
% 2.49/0.99      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.49/0.99      | l1_pre_topc(X1_53) != iProver_top
% 2.49/0.99      | l1_pre_topc(X0_53) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2824]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4541,plain,
% 2.49/0.99      ( l1_pre_topc(k1_pre_topc(sK3,sK4)) = iProver_top
% 2.49/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.49/0.99      inference(superposition,[status(thm)],[c_4535,c_3397]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_4549,plain,
% 2.49/0.99      ( l1_pre_topc(k1_pre_topc(sK3,sK4)) | ~ l1_pre_topc(sK3) ),
% 2.49/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4541]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_17,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.49/0.99      | ~ v1_tdlat_3(X1)
% 2.49/0.99      | v1_tdlat_3(X0)
% 2.49/0.99      | ~ v2_pre_topc(X1)
% 2.49/0.99      | v2_struct_0(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_33,negated_conjecture,
% 2.49/0.99      ( v2_pre_topc(sK3) ),
% 2.49/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_633,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.49/0.99      | ~ v1_tdlat_3(X1)
% 2.49/0.99      | v1_tdlat_3(X0)
% 2.49/0.99      | v2_struct_0(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | sK3 != X1 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_634,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,sK3)
% 2.49/0.99      | v1_tdlat_3(X0)
% 2.49/0.99      | ~ v1_tdlat_3(sK3)
% 2.49/0.99      | v2_struct_0(sK3)
% 2.49/0.99      | ~ l1_pre_topc(sK3) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_633]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_34,negated_conjecture,
% 2.49/0.99      ( ~ v2_struct_0(sK3) ),
% 2.49/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_32,negated_conjecture,
% 2.49/0.99      ( v1_tdlat_3(sK3) ),
% 2.49/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_636,plain,
% 2.49/0.99      ( v1_tdlat_3(X0) | ~ m1_pre_topc(X0,sK3) ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_634,c_34,c_32,c_31]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_637,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,sK3) | v1_tdlat_3(X0) ),
% 2.49/0.99      inference(renaming,[status(thm)],[c_636]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2805,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0_53,sK3) | v1_tdlat_3(X0_53) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_637]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3950,plain,
% 2.49/0.99      ( ~ m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
% 2.49/0.99      | v1_tdlat_3(k1_pre_topc(sK3,sK4)) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2805]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3870,plain,
% 2.49/0.99      ( sK4 != X0_54
% 2.49/0.99      | sK3 != X0_53
% 2.49/0.99      | v2_tex_2(X0_54,X0_53) != iProver_top
% 2.49/0.99      | v2_tex_2(sK4,sK3) = iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_3869]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3872,plain,
% 2.49/0.99      ( sK4 != k1_xboole_0
% 2.49/0.99      | sK3 != sK3
% 2.49/0.99      | v2_tex_2(sK4,sK3) = iProver_top
% 2.49/0.99      | v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_3870]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3871,plain,
% 2.49/0.99      ( v2_tex_2(sK4,sK3)
% 2.49/0.99      | ~ v2_tex_2(k1_xboole_0,sK3)
% 2.49/0.99      | sK4 != k1_xboole_0
% 2.49/0.99      | sK3 != sK3 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_3869]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2835,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3805,plain,
% 2.49/0.99      ( sK4 = sK4 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2835]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_27,plain,
% 2.49/0.99      ( v2_tex_2(u1_struct_0(X0),X1)
% 2.49/0.99      | ~ m1_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ v1_tdlat_3(X0)
% 2.49/0.99      | v2_struct_0(X1)
% 2.49/0.99      | v2_struct_0(X0)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_15,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.49/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_192,plain,
% 2.49/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.49/0.99      | v2_tex_2(u1_struct_0(X0),X1)
% 2.49/0.99      | ~ v1_tdlat_3(X0)
% 2.49/0.99      | v2_struct_0(X1)
% 2.49/0.99      | v2_struct_0(X0)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(global_propositional_subsumption,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_27,c_15]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_193,plain,
% 2.49/0.99      ( v2_tex_2(u1_struct_0(X0),X1)
% 2.49/0.99      | ~ m1_pre_topc(X0,X1)
% 2.49/0.99      | ~ v1_tdlat_3(X0)
% 2.49/0.99      | v2_struct_0(X0)
% 2.49/0.99      | v2_struct_0(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(renaming,[status(thm)],[c_192]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2809,plain,
% 2.49/0.99      ( v2_tex_2(u1_struct_0(X0_53),X1_53)
% 2.49/0.99      | ~ m1_pre_topc(X0_53,X1_53)
% 2.49/0.99      | ~ v1_tdlat_3(X0_53)
% 2.49/0.99      | v2_struct_0(X1_53)
% 2.49/0.99      | v2_struct_0(X0_53)
% 2.49/0.99      | ~ l1_pre_topc(X1_53) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_193]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3747,plain,
% 2.49/0.99      ( v2_tex_2(u1_struct_0(k1_pre_topc(sK3,sK4)),sK3)
% 2.49/0.99      | ~ m1_pre_topc(k1_pre_topc(sK3,sK4),sK3)
% 2.49/0.99      | ~ v1_tdlat_3(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | v2_struct_0(k1_pre_topc(sK3,sK4))
% 2.49/0.99      | v2_struct_0(sK3)
% 2.49/0.99      | ~ l1_pre_topc(sK3) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2809]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_12,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.49/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2823,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/0.99      | ~ l1_pre_topc(X0_53)
% 2.49/0.99      | u1_struct_0(k1_pre_topc(X0_53,X0_54)) = X0_54 ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3676,plain,
% 2.49/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/0.99      | ~ l1_pre_topc(sK3)
% 2.49/0.99      | u1_struct_0(k1_pre_topc(sK3,sK4)) = sK4 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2823]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3659,plain,
% 2.49/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_53))) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2826]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3663,plain,
% 2.49/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_3659]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_13,plain,
% 2.49/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.49/0.99      | v4_pre_topc(X1,X0)
% 2.49/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.49/0.99      | ~ l1_pre_topc(X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_26,plain,
% 2.49/0.99      ( v3_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ v1_tdlat_3(X1)
% 2.49/0.99      | ~ v2_pre_topc(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_441,plain,
% 2.49/0.99      ( v4_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.49/0.99      | ~ v1_tdlat_3(X3)
% 2.49/0.99      | ~ v2_pre_topc(X3)
% 2.49/0.99      | ~ l1_pre_topc(X1)
% 2.49/0.99      | ~ l1_pre_topc(X3)
% 2.49/0.99      | X3 != X1
% 2.49/0.99      | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
% 2.49/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_442,plain,
% 2.49/0.99      ( v4_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ v1_tdlat_3(X1)
% 2.49/0.99      | ~ v2_pre_topc(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(unflattening,[status(thm)],[c_441]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_16,plain,
% 2.49/0.99      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.49/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_5,plain,
% 2.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.49/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.49/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_458,plain,
% 2.49/0.99      ( v4_pre_topc(X0,X1)
% 2.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.99      | ~ v1_tdlat_3(X1)
% 2.49/0.99      | ~ l1_pre_topc(X1) ),
% 2.49/0.99      inference(forward_subsumption_resolution,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_442,c_16,c_5]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2807,plain,
% 2.49/0.99      ( v4_pre_topc(X0_54,X0_53)
% 2.49/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 2.49/0.99      | ~ v1_tdlat_3(X0_53)
% 2.49/0.99      | ~ l1_pre_topc(X0_53) ),
% 2.49/0.99      inference(subtyping,[status(esa)],[c_458]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_3655,plain,
% 2.49/0.99      ( v4_pre_topc(sK4,sK3)
% 2.49/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.49/0.99      | ~ v1_tdlat_3(sK3)
% 2.49/0.99      | ~ l1_pre_topc(sK3) ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2807]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2866,plain,
% 2.49/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2835]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2834,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_2865,plain,
% 2.49/0.99      ( sK3 = sK3 ),
% 2.49/0.99      inference(instantiation,[status(thm)],[c_2834]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_29,negated_conjecture,
% 2.49/0.99      ( ~ v2_tex_2(sK4,sK3) ),
% 2.49/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(c_40,plain,
% 2.49/0.99      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 2.49/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.49/0.99  
% 2.49/0.99  cnf(contradiction,plain,
% 2.49/0.99      ( $false ),
% 2.49/0.99      inference(minisat,
% 2.49/0.99                [status(thm)],
% 2.49/0.99                [c_7274,c_6188,c_6056,c_6044,c_5138,c_4898,c_4750,c_4549,
% 2.49/0.99                 c_3950,c_3872,c_3871,c_3805,c_3747,c_3683,c_3676,c_3663,
% 2.49/0.99                 c_3655,c_2866,c_2865,c_40,c_29,c_30,c_38,c_31,c_32,c_34]) ).
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/0.99  
% 2.49/0.99  ------                               Statistics
% 2.49/0.99  
% 2.49/0.99  ------ General
% 2.49/0.99  
% 2.49/0.99  abstr_ref_over_cycles:                  0
% 2.49/0.99  abstr_ref_under_cycles:                 0
% 2.49/0.99  gc_basic_clause_elim:                   0
% 2.49/0.99  forced_gc_time:                         0
% 2.49/0.99  parsing_time:                           0.033
% 2.49/0.99  unif_index_cands_time:                  0.
% 2.49/0.99  unif_index_add_time:                    0.
% 2.49/0.99  orderings_time:                         0.
% 2.49/0.99  out_proof_time:                         0.01
% 2.49/0.99  total_time:                             0.219
% 2.49/0.99  num_of_symbols:                         60
% 2.49/0.99  num_of_terms:                           5366
% 2.49/0.99  
% 2.49/0.99  ------ Preprocessing
% 2.49/0.99  
% 2.49/0.99  num_of_splits:                          0
% 2.49/0.99  num_of_split_atoms:                     0
% 2.49/0.99  num_of_reused_defs:                     0
% 2.49/0.99  num_eq_ax_congr_red:                    42
% 2.49/0.99  num_of_sem_filtered_clauses:            1
% 2.49/0.99  num_of_subtypes:                        4
% 2.49/0.99  monotx_restored_types:                  0
% 2.49/0.99  sat_num_of_epr_types:                   0
% 2.49/0.99  sat_num_of_non_cyclic_types:            0
% 2.49/0.99  sat_guarded_non_collapsed_types:        1
% 2.49/0.99  num_pure_diseq_elim:                    0
% 2.49/0.99  simp_replaced_by:                       0
% 2.49/0.99  res_preprocessed:                       156
% 2.49/0.99  prep_upred:                             0
% 2.49/0.99  prep_unflattend:                        123
% 2.49/0.99  smt_new_axioms:                         0
% 2.49/0.99  pred_elim_cands:                        8
% 2.49/0.99  pred_elim:                              4
% 2.49/0.99  pred_elim_cl:                           7
% 2.49/0.99  pred_elim_cycles:                       13
% 2.49/0.99  merged_defs:                            0
% 2.49/0.99  merged_defs_ncl:                        0
% 2.49/0.99  bin_hyper_res:                          0
% 2.49/0.99  prep_cycles:                            4
% 2.49/0.99  pred_elim_time:                         0.041
% 2.49/0.99  splitting_time:                         0.
% 2.49/0.99  sem_filter_time:                        0.
% 2.49/0.99  monotx_time:                            0.
% 2.49/0.99  subtype_inf_time:                       0.
% 2.49/0.99  
% 2.49/0.99  ------ Problem properties
% 2.49/0.99  
% 2.49/0.99  clauses:                                28
% 2.49/0.99  conjectures:                            5
% 2.49/0.99  epr:                                    8
% 2.49/0.99  horn:                                   23
% 2.49/0.99  ground:                                 5
% 2.49/0.99  unary:                                  8
% 2.49/0.99  binary:                                 5
% 2.49/0.99  lits:                                   86
% 2.49/0.99  lits_eq:                                8
% 2.49/0.99  fd_pure:                                0
% 2.49/0.99  fd_pseudo:                              0
% 2.49/0.99  fd_cond:                                1
% 2.49/0.99  fd_pseudo_cond:                         0
% 2.49/0.99  ac_symbols:                             0
% 2.49/0.99  
% 2.49/0.99  ------ Propositional Solver
% 2.49/0.99  
% 2.49/0.99  prop_solver_calls:                      28
% 2.49/0.99  prop_fast_solver_calls:                 1741
% 2.49/0.99  smt_solver_calls:                       0
% 2.49/0.99  smt_fast_solver_calls:                  0
% 2.49/0.99  prop_num_of_clauses:                    1872
% 2.49/0.99  prop_preprocess_simplified:             6678
% 2.49/0.99  prop_fo_subsumed:                       58
% 2.49/0.99  prop_solver_time:                       0.
% 2.49/0.99  smt_solver_time:                        0.
% 2.49/0.99  smt_fast_solver_time:                   0.
% 2.49/0.99  prop_fast_solver_time:                  0.
% 2.49/0.99  prop_unsat_core_time:                   0.
% 2.49/0.99  
% 2.49/0.99  ------ QBF
% 2.49/0.99  
% 2.49/0.99  qbf_q_res:                              0
% 2.49/0.99  qbf_num_tautologies:                    0
% 2.49/0.99  qbf_prep_cycles:                        0
% 2.49/0.99  
% 2.49/0.99  ------ BMC1
% 2.49/0.99  
% 2.49/0.99  bmc1_current_bound:                     -1
% 2.49/0.99  bmc1_last_solved_bound:                 -1
% 2.49/0.99  bmc1_unsat_core_size:                   -1
% 2.49/0.99  bmc1_unsat_core_parents_size:           -1
% 2.49/0.99  bmc1_merge_next_fun:                    0
% 2.49/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.49/0.99  
% 2.49/0.99  ------ Instantiation
% 2.49/0.99  
% 2.49/0.99  inst_num_of_clauses:                    430
% 2.49/0.99  inst_num_in_passive:                    100
% 2.49/0.99  inst_num_in_active:                     282
% 2.49/0.99  inst_num_in_unprocessed:                48
% 2.49/0.99  inst_num_of_loops:                      320
% 2.49/0.99  inst_num_of_learning_restarts:          0
% 2.49/0.99  inst_num_moves_active_passive:          35
% 2.49/0.99  inst_lit_activity:                      0
% 2.49/0.99  inst_lit_activity_moves:                0
% 2.49/0.99  inst_num_tautologies:                   0
% 2.49/0.99  inst_num_prop_implied:                  0
% 2.49/0.99  inst_num_existing_simplified:           0
% 2.49/0.99  inst_num_eq_res_simplified:             0
% 2.49/0.99  inst_num_child_elim:                    0
% 2.49/0.99  inst_num_of_dismatching_blockings:      104
% 2.49/0.99  inst_num_of_non_proper_insts:           369
% 2.49/0.99  inst_num_of_duplicates:                 0
% 2.49/0.99  inst_inst_num_from_inst_to_res:         0
% 2.49/0.99  inst_dismatching_checking_time:         0.
% 2.49/0.99  
% 2.49/0.99  ------ Resolution
% 2.49/0.99  
% 2.49/0.99  res_num_of_clauses:                     0
% 2.49/0.99  res_num_in_passive:                     0
% 2.49/0.99  res_num_in_active:                      0
% 2.49/0.99  res_num_of_loops:                       160
% 2.49/0.99  res_forward_subset_subsumed:            28
% 2.49/0.99  res_backward_subset_subsumed:           0
% 2.49/0.99  res_forward_subsumed:                   0
% 2.49/0.99  res_backward_subsumed:                  0
% 2.49/0.99  res_forward_subsumption_resolution:     7
% 2.49/0.99  res_backward_subsumption_resolution:    0
% 2.49/0.99  res_clause_to_clause_subsumption:       300
% 2.49/0.99  res_orphan_elimination:                 0
% 2.49/0.99  res_tautology_del:                      29
% 2.49/0.99  res_num_eq_res_simplified:              0
% 2.49/0.99  res_num_sel_changes:                    0
% 2.49/0.99  res_moves_from_active_to_pass:          0
% 2.49/0.99  
% 2.49/0.99  ------ Superposition
% 2.49/0.99  
% 2.49/0.99  sup_time_total:                         0.
% 2.49/0.99  sup_time_generating:                    0.
% 2.49/0.99  sup_time_sim_full:                      0.
% 2.49/0.99  sup_time_sim_immed:                     0.
% 2.49/0.99  
% 2.49/0.99  sup_num_of_clauses:                     144
% 2.49/0.99  sup_num_in_active:                      63
% 2.49/0.99  sup_num_in_passive:                     81
% 2.49/0.99  sup_num_of_loops:                       63
% 2.49/0.99  sup_fw_superposition:                   66
% 2.49/0.99  sup_bw_superposition:                   80
% 2.49/0.99  sup_immediate_simplified:               31
% 2.49/0.99  sup_given_eliminated:                   0
% 2.49/0.99  comparisons_done:                       0
% 2.49/0.99  comparisons_avoided:                    0
% 2.49/0.99  
% 2.49/0.99  ------ Simplifications
% 2.49/0.99  
% 2.49/0.99  
% 2.49/0.99  sim_fw_subset_subsumed:                 4
% 2.49/0.99  sim_bw_subset_subsumed:                 0
% 2.49/0.99  sim_fw_subsumed:                        8
% 2.49/0.99  sim_bw_subsumed:                        1
% 2.49/0.99  sim_fw_subsumption_res:                 0
% 2.49/0.99  sim_bw_subsumption_res:                 0
% 2.49/0.99  sim_tautology_del:                      1
% 2.49/0.99  sim_eq_tautology_del:                   1
% 2.49/0.99  sim_eq_res_simp:                        0
% 2.49/0.99  sim_fw_demodulated:                     2
% 2.49/0.99  sim_bw_demodulated:                     1
% 2.49/0.99  sim_light_normalised:                   20
% 2.49/0.99  sim_joinable_taut:                      0
% 2.49/0.99  sim_joinable_simp:                      0
% 2.49/0.99  sim_ac_normalised:                      0
% 2.49/0.99  sim_smt_subsumption:                    0
% 2.49/0.99  
%------------------------------------------------------------------------------
