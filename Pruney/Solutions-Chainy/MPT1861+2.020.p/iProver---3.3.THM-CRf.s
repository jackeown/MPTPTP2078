%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:51 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 577 expanded)
%              Number of clauses        :   88 ( 227 expanded)
%              Number of leaves         :   12 ( 144 expanded)
%              Depth                    :   16
%              Number of atoms          :  339 (2392 expanded)
%              Number of equality atoms :  146 ( 285 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & ( v2_tex_2(sK2,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_321,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_588,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_320,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_589,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_580,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_44))
    | k4_subset_1(X0_44,k3_subset_1(X0_44,X0_41),X1_41) = k3_subset_1(X0_44,k7_subset_1(X0_44,X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_584,plain,
    ( k4_subset_1(X0_44,k3_subset_1(X0_44,X0_41),X1_41) = k3_subset_1(X0_44,k7_subset_1(X0_44,X0_41,X1_41))
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_2366,plain,
    ( k4_subset_1(X0_44,k3_subset_1(X0_44,X0_41),k3_subset_1(X0_44,X1_41)) = k3_subset_1(X0_44,k7_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41)))
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_580,c_584])).

cnf(c_25378,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_41),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK1)))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_2366])).

cnf(c_27598,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(superposition,[status(thm)],[c_588,c_25378])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_44))
    | k9_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41)) = k7_subset_1(X0_44,X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_583,plain,
    ( k9_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41)) = k7_subset_1(X0_44,X0_41,X1_41)
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_1269,plain,
    ( k9_subset_1(X0_44,X0_41,k3_subset_1(X0_44,k3_subset_1(X0_44,X1_41))) = k7_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41))
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_580,c_583])).

cnf(c_16776,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK1))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_1269])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_582,plain,
    ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_1059,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_589,c_582])).

cnf(c_16864,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1)
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16776,c_1059])).

cnf(c_18734,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_588,c_16864])).

cnf(c_27696,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_27598,c_18734])).

cnf(c_6,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_324,plain,
    ( r1_tarski(k3_subset_1(X0_44,k4_subset_1(X0_44,X0_41,X1_41)),k3_subset_1(X0_44,X0_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_44))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_585,plain,
    ( r1_tarski(k3_subset_1(X0_44,k4_subset_1(X0_44,X0_41,X1_41)),k3_subset_1(X0_44,X0_41)) = iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_28064,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27696,c_585])).

cnf(c_1058,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_588,c_582])).

cnf(c_28065,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1))),sK2) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28064,c_1058])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | k9_subset_1(X0_44,X0_41,X1_41) = k9_subset_1(X0_44,X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_579,plain,
    ( k9_subset_1(X0_44,X0_41,X1_41) = k9_subset_1(X0_44,X1_41,X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_1047,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,X0_41) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
    inference(superposition,[status(thm)],[c_588,c_579])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | m1_subset_1(k9_subset_1(X0_44,X1_41,X0_41),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_581,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_44,X1_41,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1487,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_581])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_689,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_690,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_2755,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1487,c_15,c_690])).

cnf(c_2762,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_2755])).

cnf(c_3960,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,X0_41))) = k9_subset_1(u1_struct_0(sK0),sK2,X0_41) ),
    inference(superposition,[status(thm)],[c_2762,c_582])).

cnf(c_28066,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK2) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28065,c_3960])).

cnf(c_25377,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_41),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK2)))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_2366])).

cnf(c_27230,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(superposition,[status(thm)],[c_589,c_25377])).

cnf(c_16775,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK2))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_1269])).

cnf(c_16869,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2)
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16775,c_1058])).

cnf(c_20623,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_589,c_16869])).

cnf(c_27324,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_27230,c_20623])).

cnf(c_27734,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27324,c_585])).

cnf(c_27735,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27734,c_1059])).

cnf(c_1048,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,X0_41) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1) ),
    inference(superposition,[status(thm)],[c_589,c_579])).

cnf(c_1735,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_581])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_694,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_695,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_3761,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1735,c_14,c_695])).

cnf(c_3781,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_41,sK1))) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1) ),
    inference(superposition,[status(thm)],[c_3761,c_582])).

cnf(c_4994,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,X0_41))) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1) ),
    inference(superposition,[status(thm)],[c_1048,c_3781])).

cnf(c_27736,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27735,c_4994])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_148,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_149,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(X1,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_319,plain,
    ( ~ v2_tex_2(X0_41,sK0)
    | v2_tex_2(X1_41,sK0)
    | ~ r1_tarski(X1_41,X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_149])).

cnf(c_590,plain,
    ( v2_tex_2(X0_41,sK0) != iProver_top
    | v2_tex_2(X1_41,sK0) = iProver_top
    | r1_tarski(X1_41,X0_41) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_920,plain,
    ( v2_tex_2(X0_41,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0_41,sK2) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_590])).

cnf(c_1167,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK2) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_920])).

cnf(c_11602,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,X0_41),sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1167])).

cnf(c_12119,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11602])).

cnf(c_921,plain,
    ( v2_tex_2(X0_41,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0_41,sK1) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_590])).

cnf(c_1166,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK1) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_921])).

cnf(c_9401,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,X0_41),sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1166])).

cnf(c_9766,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9401])).

cnf(c_680,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_681,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_677,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_678,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28066,c_27736,c_12119,c_9766,c_681,c_678,c_17,c_16,c_15,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.58/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/1.49  
% 7.58/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.49  
% 7.58/1.49  ------  iProver source info
% 7.58/1.49  
% 7.58/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.49  git: non_committed_changes: false
% 7.58/1.49  git: last_make_outside_of_git: false
% 7.58/1.49  
% 7.58/1.49  ------ 
% 7.58/1.49  
% 7.58/1.49  ------ Input Options
% 7.58/1.49  
% 7.58/1.49  --out_options                           all
% 7.58/1.49  --tptp_safe_out                         true
% 7.58/1.49  --problem_path                          ""
% 7.58/1.49  --include_path                          ""
% 7.58/1.49  --clausifier                            res/vclausify_rel
% 7.58/1.49  --clausifier_options                    --mode clausify
% 7.58/1.49  --stdin                                 false
% 7.58/1.49  --stats_out                             all
% 7.58/1.49  
% 7.58/1.49  ------ General Options
% 7.58/1.49  
% 7.58/1.49  --fof                                   false
% 7.58/1.49  --time_out_real                         305.
% 7.58/1.49  --time_out_virtual                      -1.
% 7.58/1.49  --symbol_type_check                     false
% 7.58/1.49  --clausify_out                          false
% 7.58/1.49  --sig_cnt_out                           false
% 7.58/1.49  --trig_cnt_out                          false
% 7.58/1.49  --trig_cnt_out_tolerance                1.
% 7.58/1.49  --trig_cnt_out_sk_spl                   false
% 7.58/1.49  --abstr_cl_out                          false
% 7.58/1.49  
% 7.58/1.49  ------ Global Options
% 7.58/1.49  
% 7.58/1.49  --schedule                              default
% 7.58/1.49  --add_important_lit                     false
% 7.58/1.49  --prop_solver_per_cl                    1000
% 7.58/1.49  --min_unsat_core                        false
% 7.58/1.49  --soft_assumptions                      false
% 7.58/1.49  --soft_lemma_size                       3
% 7.58/1.49  --prop_impl_unit_size                   0
% 7.58/1.49  --prop_impl_unit                        []
% 7.58/1.49  --share_sel_clauses                     true
% 7.58/1.49  --reset_solvers                         false
% 7.58/1.49  --bc_imp_inh                            [conj_cone]
% 7.58/1.49  --conj_cone_tolerance                   3.
% 7.58/1.49  --extra_neg_conj                        none
% 7.58/1.49  --large_theory_mode                     true
% 7.58/1.49  --prolific_symb_bound                   200
% 7.58/1.49  --lt_threshold                          2000
% 7.58/1.49  --clause_weak_htbl                      true
% 7.58/1.49  --gc_record_bc_elim                     false
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing Options
% 7.58/1.49  
% 7.58/1.49  --preprocessing_flag                    true
% 7.58/1.49  --time_out_prep_mult                    0.1
% 7.58/1.49  --splitting_mode                        input
% 7.58/1.49  --splitting_grd                         true
% 7.58/1.49  --splitting_cvd                         false
% 7.58/1.49  --splitting_cvd_svl                     false
% 7.58/1.49  --splitting_nvd                         32
% 7.58/1.49  --sub_typing                            true
% 7.58/1.49  --prep_gs_sim                           true
% 7.58/1.49  --prep_unflatten                        true
% 7.58/1.49  --prep_res_sim                          true
% 7.58/1.49  --prep_upred                            true
% 7.58/1.49  --prep_sem_filter                       exhaustive
% 7.58/1.49  --prep_sem_filter_out                   false
% 7.58/1.49  --pred_elim                             true
% 7.58/1.49  --res_sim_input                         true
% 7.58/1.49  --eq_ax_congr_red                       true
% 7.58/1.49  --pure_diseq_elim                       true
% 7.58/1.49  --brand_transform                       false
% 7.58/1.49  --non_eq_to_eq                          false
% 7.58/1.49  --prep_def_merge                        true
% 7.58/1.49  --prep_def_merge_prop_impl              false
% 7.58/1.49  --prep_def_merge_mbd                    true
% 7.58/1.49  --prep_def_merge_tr_red                 false
% 7.58/1.49  --prep_def_merge_tr_cl                  false
% 7.58/1.49  --smt_preprocessing                     true
% 7.58/1.49  --smt_ac_axioms                         fast
% 7.58/1.49  --preprocessed_out                      false
% 7.58/1.49  --preprocessed_stats                    false
% 7.58/1.49  
% 7.58/1.49  ------ Abstraction refinement Options
% 7.58/1.49  
% 7.58/1.49  --abstr_ref                             []
% 7.58/1.49  --abstr_ref_prep                        false
% 7.58/1.49  --abstr_ref_until_sat                   false
% 7.58/1.49  --abstr_ref_sig_restrict                funpre
% 7.58/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.49  --abstr_ref_under                       []
% 7.58/1.49  
% 7.58/1.49  ------ SAT Options
% 7.58/1.49  
% 7.58/1.49  --sat_mode                              false
% 7.58/1.49  --sat_fm_restart_options                ""
% 7.58/1.49  --sat_gr_def                            false
% 7.58/1.49  --sat_epr_types                         true
% 7.58/1.49  --sat_non_cyclic_types                  false
% 7.58/1.49  --sat_finite_models                     false
% 7.58/1.49  --sat_fm_lemmas                         false
% 7.58/1.49  --sat_fm_prep                           false
% 7.58/1.49  --sat_fm_uc_incr                        true
% 7.58/1.49  --sat_out_model                         small
% 7.58/1.49  --sat_out_clauses                       false
% 7.58/1.49  
% 7.58/1.49  ------ QBF Options
% 7.58/1.49  
% 7.58/1.49  --qbf_mode                              false
% 7.58/1.49  --qbf_elim_univ                         false
% 7.58/1.49  --qbf_dom_inst                          none
% 7.58/1.49  --qbf_dom_pre_inst                      false
% 7.58/1.49  --qbf_sk_in                             false
% 7.58/1.49  --qbf_pred_elim                         true
% 7.58/1.49  --qbf_split                             512
% 7.58/1.49  
% 7.58/1.49  ------ BMC1 Options
% 7.58/1.49  
% 7.58/1.49  --bmc1_incremental                      false
% 7.58/1.49  --bmc1_axioms                           reachable_all
% 7.58/1.49  --bmc1_min_bound                        0
% 7.58/1.49  --bmc1_max_bound                        -1
% 7.58/1.49  --bmc1_max_bound_default                -1
% 7.58/1.49  --bmc1_symbol_reachability              true
% 7.58/1.49  --bmc1_property_lemmas                  false
% 7.58/1.49  --bmc1_k_induction                      false
% 7.58/1.49  --bmc1_non_equiv_states                 false
% 7.58/1.49  --bmc1_deadlock                         false
% 7.58/1.49  --bmc1_ucm                              false
% 7.58/1.49  --bmc1_add_unsat_core                   none
% 7.58/1.49  --bmc1_unsat_core_children              false
% 7.58/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.49  --bmc1_out_stat                         full
% 7.58/1.49  --bmc1_ground_init                      false
% 7.58/1.49  --bmc1_pre_inst_next_state              false
% 7.58/1.49  --bmc1_pre_inst_state                   false
% 7.58/1.49  --bmc1_pre_inst_reach_state             false
% 7.58/1.49  --bmc1_out_unsat_core                   false
% 7.58/1.49  --bmc1_aig_witness_out                  false
% 7.58/1.49  --bmc1_verbose                          false
% 7.58/1.49  --bmc1_dump_clauses_tptp                false
% 7.58/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.49  --bmc1_dump_file                        -
% 7.58/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.49  --bmc1_ucm_extend_mode                  1
% 7.58/1.49  --bmc1_ucm_init_mode                    2
% 7.58/1.49  --bmc1_ucm_cone_mode                    none
% 7.58/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.49  --bmc1_ucm_relax_model                  4
% 7.58/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.49  --bmc1_ucm_layered_model                none
% 7.58/1.49  --bmc1_ucm_max_lemma_size               10
% 7.58/1.49  
% 7.58/1.49  ------ AIG Options
% 7.58/1.49  
% 7.58/1.49  --aig_mode                              false
% 7.58/1.49  
% 7.58/1.49  ------ Instantiation Options
% 7.58/1.49  
% 7.58/1.49  --instantiation_flag                    true
% 7.58/1.49  --inst_sos_flag                         false
% 7.58/1.49  --inst_sos_phase                        true
% 7.58/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel_side                     num_symb
% 7.58/1.49  --inst_solver_per_active                1400
% 7.58/1.49  --inst_solver_calls_frac                1.
% 7.58/1.49  --inst_passive_queue_type               priority_queues
% 7.58/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.49  --inst_passive_queues_freq              [25;2]
% 7.58/1.49  --inst_dismatching                      true
% 7.58/1.49  --inst_eager_unprocessed_to_passive     true
% 7.58/1.49  --inst_prop_sim_given                   true
% 7.58/1.49  --inst_prop_sim_new                     false
% 7.58/1.49  --inst_subs_new                         false
% 7.58/1.49  --inst_eq_res_simp                      false
% 7.58/1.49  --inst_subs_given                       false
% 7.58/1.49  --inst_orphan_elimination               true
% 7.58/1.49  --inst_learning_loop_flag               true
% 7.58/1.49  --inst_learning_start                   3000
% 7.58/1.49  --inst_learning_factor                  2
% 7.58/1.49  --inst_start_prop_sim_after_learn       3
% 7.58/1.49  --inst_sel_renew                        solver
% 7.58/1.49  --inst_lit_activity_flag                true
% 7.58/1.49  --inst_restr_to_given                   false
% 7.58/1.49  --inst_activity_threshold               500
% 7.58/1.49  --inst_out_proof                        true
% 7.58/1.49  
% 7.58/1.49  ------ Resolution Options
% 7.58/1.49  
% 7.58/1.49  --resolution_flag                       true
% 7.58/1.49  --res_lit_sel                           adaptive
% 7.58/1.49  --res_lit_sel_side                      none
% 7.58/1.49  --res_ordering                          kbo
% 7.58/1.49  --res_to_prop_solver                    active
% 7.58/1.49  --res_prop_simpl_new                    false
% 7.58/1.49  --res_prop_simpl_given                  true
% 7.58/1.49  --res_passive_queue_type                priority_queues
% 7.58/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.49  --res_passive_queues_freq               [15;5]
% 7.58/1.49  --res_forward_subs                      full
% 7.58/1.49  --res_backward_subs                     full
% 7.58/1.49  --res_forward_subs_resolution           true
% 7.58/1.49  --res_backward_subs_resolution          true
% 7.58/1.49  --res_orphan_elimination                true
% 7.58/1.49  --res_time_limit                        2.
% 7.58/1.49  --res_out_proof                         true
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Options
% 7.58/1.49  
% 7.58/1.49  --superposition_flag                    true
% 7.58/1.49  --sup_passive_queue_type                priority_queues
% 7.58/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.49  --demod_completeness_check              fast
% 7.58/1.49  --demod_use_ground                      true
% 7.58/1.49  --sup_to_prop_solver                    passive
% 7.58/1.49  --sup_prop_simpl_new                    true
% 7.58/1.49  --sup_prop_simpl_given                  true
% 7.58/1.49  --sup_fun_splitting                     false
% 7.58/1.49  --sup_smt_interval                      50000
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Simplification Setup
% 7.58/1.49  
% 7.58/1.49  --sup_indices_passive                   []
% 7.58/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.49  --sup_full_bw                           [BwDemod]
% 7.58/1.49  --sup_immed_triv                        [TrivRules]
% 7.58/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.49  --sup_immed_bw_main                     []
% 7.58/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.49  
% 7.58/1.49  ------ Combination Options
% 7.58/1.49  
% 7.58/1.49  --comb_res_mult                         3
% 7.58/1.49  --comb_sup_mult                         2
% 7.58/1.49  --comb_inst_mult                        10
% 7.58/1.49  
% 7.58/1.49  ------ Debug Options
% 7.58/1.49  
% 7.58/1.49  --dbg_backtrace                         false
% 7.58/1.49  --dbg_dump_prop_clauses                 false
% 7.58/1.49  --dbg_dump_prop_clauses_file            -
% 7.58/1.49  --dbg_out_stat                          false
% 7.58/1.49  ------ Parsing...
% 7.58/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.49  ------ Proving...
% 7.58/1.49  ------ Problem Properties 
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  clauses                                 12
% 7.58/1.49  conjectures                             4
% 7.58/1.49  EPR                                     1
% 7.58/1.49  Horn                                    11
% 7.58/1.49  unary                                   3
% 7.58/1.49  binary                                  5
% 7.58/1.49  lits                                    27
% 7.58/1.49  lits eq                                 4
% 7.58/1.49  fd_pure                                 0
% 7.58/1.49  fd_pseudo                               0
% 7.58/1.49  fd_cond                                 0
% 7.58/1.49  fd_pseudo_cond                          0
% 7.58/1.49  AC symbols                              0
% 7.58/1.49  
% 7.58/1.49  ------ Schedule dynamic 5 is on 
% 7.58/1.49  
% 7.58/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  ------ 
% 7.58/1.49  Current options:
% 7.58/1.49  ------ 
% 7.58/1.49  
% 7.58/1.49  ------ Input Options
% 7.58/1.49  
% 7.58/1.49  --out_options                           all
% 7.58/1.49  --tptp_safe_out                         true
% 7.58/1.49  --problem_path                          ""
% 7.58/1.49  --include_path                          ""
% 7.58/1.49  --clausifier                            res/vclausify_rel
% 7.58/1.49  --clausifier_options                    --mode clausify
% 7.58/1.49  --stdin                                 false
% 7.58/1.49  --stats_out                             all
% 7.58/1.49  
% 7.58/1.49  ------ General Options
% 7.58/1.49  
% 7.58/1.49  --fof                                   false
% 7.58/1.49  --time_out_real                         305.
% 7.58/1.49  --time_out_virtual                      -1.
% 7.58/1.49  --symbol_type_check                     false
% 7.58/1.49  --clausify_out                          false
% 7.58/1.49  --sig_cnt_out                           false
% 7.58/1.49  --trig_cnt_out                          false
% 7.58/1.49  --trig_cnt_out_tolerance                1.
% 7.58/1.49  --trig_cnt_out_sk_spl                   false
% 7.58/1.49  --abstr_cl_out                          false
% 7.58/1.49  
% 7.58/1.49  ------ Global Options
% 7.58/1.49  
% 7.58/1.49  --schedule                              default
% 7.58/1.49  --add_important_lit                     false
% 7.58/1.49  --prop_solver_per_cl                    1000
% 7.58/1.49  --min_unsat_core                        false
% 7.58/1.49  --soft_assumptions                      false
% 7.58/1.49  --soft_lemma_size                       3
% 7.58/1.49  --prop_impl_unit_size                   0
% 7.58/1.49  --prop_impl_unit                        []
% 7.58/1.49  --share_sel_clauses                     true
% 7.58/1.49  --reset_solvers                         false
% 7.58/1.49  --bc_imp_inh                            [conj_cone]
% 7.58/1.49  --conj_cone_tolerance                   3.
% 7.58/1.49  --extra_neg_conj                        none
% 7.58/1.49  --large_theory_mode                     true
% 7.58/1.49  --prolific_symb_bound                   200
% 7.58/1.49  --lt_threshold                          2000
% 7.58/1.49  --clause_weak_htbl                      true
% 7.58/1.49  --gc_record_bc_elim                     false
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing Options
% 7.58/1.49  
% 7.58/1.49  --preprocessing_flag                    true
% 7.58/1.49  --time_out_prep_mult                    0.1
% 7.58/1.49  --splitting_mode                        input
% 7.58/1.49  --splitting_grd                         true
% 7.58/1.49  --splitting_cvd                         false
% 7.58/1.49  --splitting_cvd_svl                     false
% 7.58/1.49  --splitting_nvd                         32
% 7.58/1.49  --sub_typing                            true
% 7.58/1.49  --prep_gs_sim                           true
% 7.58/1.49  --prep_unflatten                        true
% 7.58/1.49  --prep_res_sim                          true
% 7.58/1.49  --prep_upred                            true
% 7.58/1.49  --prep_sem_filter                       exhaustive
% 7.58/1.49  --prep_sem_filter_out                   false
% 7.58/1.49  --pred_elim                             true
% 7.58/1.49  --res_sim_input                         true
% 7.58/1.49  --eq_ax_congr_red                       true
% 7.58/1.49  --pure_diseq_elim                       true
% 7.58/1.49  --brand_transform                       false
% 7.58/1.49  --non_eq_to_eq                          false
% 7.58/1.49  --prep_def_merge                        true
% 7.58/1.49  --prep_def_merge_prop_impl              false
% 7.58/1.49  --prep_def_merge_mbd                    true
% 7.58/1.49  --prep_def_merge_tr_red                 false
% 7.58/1.49  --prep_def_merge_tr_cl                  false
% 7.58/1.49  --smt_preprocessing                     true
% 7.58/1.49  --smt_ac_axioms                         fast
% 7.58/1.49  --preprocessed_out                      false
% 7.58/1.49  --preprocessed_stats                    false
% 7.58/1.49  
% 7.58/1.49  ------ Abstraction refinement Options
% 7.58/1.49  
% 7.58/1.49  --abstr_ref                             []
% 7.58/1.49  --abstr_ref_prep                        false
% 7.58/1.49  --abstr_ref_until_sat                   false
% 7.58/1.49  --abstr_ref_sig_restrict                funpre
% 7.58/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.49  --abstr_ref_under                       []
% 7.58/1.49  
% 7.58/1.49  ------ SAT Options
% 7.58/1.49  
% 7.58/1.49  --sat_mode                              false
% 7.58/1.49  --sat_fm_restart_options                ""
% 7.58/1.49  --sat_gr_def                            false
% 7.58/1.49  --sat_epr_types                         true
% 7.58/1.49  --sat_non_cyclic_types                  false
% 7.58/1.49  --sat_finite_models                     false
% 7.58/1.49  --sat_fm_lemmas                         false
% 7.58/1.49  --sat_fm_prep                           false
% 7.58/1.49  --sat_fm_uc_incr                        true
% 7.58/1.49  --sat_out_model                         small
% 7.58/1.49  --sat_out_clauses                       false
% 7.58/1.49  
% 7.58/1.49  ------ QBF Options
% 7.58/1.49  
% 7.58/1.49  --qbf_mode                              false
% 7.58/1.49  --qbf_elim_univ                         false
% 7.58/1.49  --qbf_dom_inst                          none
% 7.58/1.49  --qbf_dom_pre_inst                      false
% 7.58/1.49  --qbf_sk_in                             false
% 7.58/1.49  --qbf_pred_elim                         true
% 7.58/1.49  --qbf_split                             512
% 7.58/1.49  
% 7.58/1.49  ------ BMC1 Options
% 7.58/1.49  
% 7.58/1.49  --bmc1_incremental                      false
% 7.58/1.49  --bmc1_axioms                           reachable_all
% 7.58/1.49  --bmc1_min_bound                        0
% 7.58/1.49  --bmc1_max_bound                        -1
% 7.58/1.49  --bmc1_max_bound_default                -1
% 7.58/1.49  --bmc1_symbol_reachability              true
% 7.58/1.49  --bmc1_property_lemmas                  false
% 7.58/1.49  --bmc1_k_induction                      false
% 7.58/1.49  --bmc1_non_equiv_states                 false
% 7.58/1.49  --bmc1_deadlock                         false
% 7.58/1.49  --bmc1_ucm                              false
% 7.58/1.49  --bmc1_add_unsat_core                   none
% 7.58/1.49  --bmc1_unsat_core_children              false
% 7.58/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.49  --bmc1_out_stat                         full
% 7.58/1.49  --bmc1_ground_init                      false
% 7.58/1.49  --bmc1_pre_inst_next_state              false
% 7.58/1.49  --bmc1_pre_inst_state                   false
% 7.58/1.49  --bmc1_pre_inst_reach_state             false
% 7.58/1.49  --bmc1_out_unsat_core                   false
% 7.58/1.49  --bmc1_aig_witness_out                  false
% 7.58/1.49  --bmc1_verbose                          false
% 7.58/1.49  --bmc1_dump_clauses_tptp                false
% 7.58/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.49  --bmc1_dump_file                        -
% 7.58/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.49  --bmc1_ucm_extend_mode                  1
% 7.58/1.49  --bmc1_ucm_init_mode                    2
% 7.58/1.49  --bmc1_ucm_cone_mode                    none
% 7.58/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.49  --bmc1_ucm_relax_model                  4
% 7.58/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.49  --bmc1_ucm_layered_model                none
% 7.58/1.49  --bmc1_ucm_max_lemma_size               10
% 7.58/1.49  
% 7.58/1.49  ------ AIG Options
% 7.58/1.49  
% 7.58/1.49  --aig_mode                              false
% 7.58/1.49  
% 7.58/1.49  ------ Instantiation Options
% 7.58/1.49  
% 7.58/1.49  --instantiation_flag                    true
% 7.58/1.49  --inst_sos_flag                         false
% 7.58/1.49  --inst_sos_phase                        true
% 7.58/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel_side                     none
% 7.58/1.49  --inst_solver_per_active                1400
% 7.58/1.49  --inst_solver_calls_frac                1.
% 7.58/1.49  --inst_passive_queue_type               priority_queues
% 7.58/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.49  --inst_passive_queues_freq              [25;2]
% 7.58/1.49  --inst_dismatching                      true
% 7.58/1.49  --inst_eager_unprocessed_to_passive     true
% 7.58/1.49  --inst_prop_sim_given                   true
% 7.58/1.49  --inst_prop_sim_new                     false
% 7.58/1.49  --inst_subs_new                         false
% 7.58/1.49  --inst_eq_res_simp                      false
% 7.58/1.49  --inst_subs_given                       false
% 7.58/1.49  --inst_orphan_elimination               true
% 7.58/1.49  --inst_learning_loop_flag               true
% 7.58/1.49  --inst_learning_start                   3000
% 7.58/1.49  --inst_learning_factor                  2
% 7.58/1.49  --inst_start_prop_sim_after_learn       3
% 7.58/1.49  --inst_sel_renew                        solver
% 7.58/1.49  --inst_lit_activity_flag                true
% 7.58/1.49  --inst_restr_to_given                   false
% 7.58/1.49  --inst_activity_threshold               500
% 7.58/1.49  --inst_out_proof                        true
% 7.58/1.49  
% 7.58/1.49  ------ Resolution Options
% 7.58/1.49  
% 7.58/1.49  --resolution_flag                       false
% 7.58/1.49  --res_lit_sel                           adaptive
% 7.58/1.49  --res_lit_sel_side                      none
% 7.58/1.49  --res_ordering                          kbo
% 7.58/1.49  --res_to_prop_solver                    active
% 7.58/1.49  --res_prop_simpl_new                    false
% 7.58/1.49  --res_prop_simpl_given                  true
% 7.58/1.49  --res_passive_queue_type                priority_queues
% 7.58/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.49  --res_passive_queues_freq               [15;5]
% 7.58/1.49  --res_forward_subs                      full
% 7.58/1.49  --res_backward_subs                     full
% 7.58/1.49  --res_forward_subs_resolution           true
% 7.58/1.49  --res_backward_subs_resolution          true
% 7.58/1.49  --res_orphan_elimination                true
% 7.58/1.49  --res_time_limit                        2.
% 7.58/1.49  --res_out_proof                         true
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Options
% 7.58/1.49  
% 7.58/1.49  --superposition_flag                    true
% 7.58/1.49  --sup_passive_queue_type                priority_queues
% 7.58/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.49  --demod_completeness_check              fast
% 7.58/1.49  --demod_use_ground                      true
% 7.58/1.49  --sup_to_prop_solver                    passive
% 7.58/1.49  --sup_prop_simpl_new                    true
% 7.58/1.49  --sup_prop_simpl_given                  true
% 7.58/1.49  --sup_fun_splitting                     false
% 7.58/1.49  --sup_smt_interval                      50000
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Simplification Setup
% 7.58/1.49  
% 7.58/1.49  --sup_indices_passive                   []
% 7.58/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.49  --sup_full_bw                           [BwDemod]
% 7.58/1.49  --sup_immed_triv                        [TrivRules]
% 7.58/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_immed_bw_main                     []
% 7.58/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.50  
% 7.58/1.50  ------ Combination Options
% 7.58/1.50  
% 7.58/1.50  --comb_res_mult                         3
% 7.58/1.50  --comb_sup_mult                         2
% 7.58/1.50  --comb_inst_mult                        10
% 7.58/1.50  
% 7.58/1.50  ------ Debug Options
% 7.58/1.50  
% 7.58/1.50  --dbg_backtrace                         false
% 7.58/1.50  --dbg_dump_prop_clauses                 false
% 7.58/1.50  --dbg_dump_prop_clauses_file            -
% 7.58/1.50  --dbg_out_stat                          false
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ Proving...
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS status Theorem for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  fof(f9,conjecture,(
% 7.58/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f10,negated_conjecture,(
% 7.58/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.58/1.50    inference(negated_conjecture,[],[f9])).
% 7.58/1.50  
% 7.58/1.50  fof(f20,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f10])).
% 7.58/1.50  
% 7.58/1.50  fof(f21,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.58/1.50    inference(flattening,[],[f20])).
% 7.58/1.50  
% 7.58/1.50  fof(f24,plain,(
% 7.58/1.50    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f23,plain,(
% 7.58/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f22,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f25,plain,(
% 7.58/1.50    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.58/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).
% 7.58/1.50  
% 7.58/1.50  fof(f36,plain,(
% 7.58/1.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f35,plain,(
% 7.58/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f2,axiom,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f12,plain,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f2])).
% 7.58/1.50  
% 7.58/1.50  fof(f27,plain,(
% 7.58/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f12])).
% 7.58/1.50  
% 7.58/1.50  fof(f6,axiom,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f16,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f6])).
% 7.58/1.50  
% 7.58/1.50  fof(f31,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f16])).
% 7.58/1.50  
% 7.58/1.50  fof(f5,axiom,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f15,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f5])).
% 7.58/1.50  
% 7.58/1.50  fof(f30,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f15])).
% 7.58/1.50  
% 7.58/1.50  fof(f4,axiom,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f14,plain,(
% 7.58/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f4])).
% 7.58/1.50  
% 7.58/1.50  fof(f29,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f14])).
% 7.58/1.50  
% 7.58/1.50  fof(f7,axiom,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f17,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f7])).
% 7.58/1.50  
% 7.58/1.50  fof(f32,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f17])).
% 7.58/1.50  
% 7.58/1.50  fof(f1,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f11,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f1])).
% 7.58/1.50  
% 7.58/1.50  fof(f26,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f11])).
% 7.58/1.50  
% 7.58/1.50  fof(f3,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f13,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f3])).
% 7.58/1.50  
% 7.58/1.50  fof(f28,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f13])).
% 7.58/1.50  
% 7.58/1.50  fof(f8,axiom,(
% 7.58/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 7.58/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f18,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f8])).
% 7.58/1.50  
% 7.58/1.50  fof(f19,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.58/1.50    inference(flattening,[],[f18])).
% 7.58/1.50  
% 7.58/1.50  fof(f33,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f19])).
% 7.58/1.50  
% 7.58/1.50  fof(f34,plain,(
% 7.58/1.50    l1_pre_topc(sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f38,plain,(
% 7.58/1.50    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f37,plain,(
% 7.58/1.50    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_321,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_588,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_320,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_589,plain,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_329,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_580,plain,
% 7.58/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.58/1.50      | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_325,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | k4_subset_1(X0_44,k3_subset_1(X0_44,X0_41),X1_41) = k3_subset_1(X0_44,k7_subset_1(X0_44,X0_41,X1_41)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_584,plain,
% 7.58/1.50      ( k4_subset_1(X0_44,k3_subset_1(X0_44,X0_41),X1_41) = k3_subset_1(X0_44,k7_subset_1(X0_44,X0_41,X1_41))
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2366,plain,
% 7.58/1.50      ( k4_subset_1(X0_44,k3_subset_1(X0_44,X0_41),k3_subset_1(X0_44,X1_41)) = k3_subset_1(X0_44,k7_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41)))
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_580,c_584]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25378,plain,
% 7.58/1.50      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_41),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK1)))
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_2366]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27598,plain,
% 7.58/1.50      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1))) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_25378]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.58/1.50      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_326,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | k9_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41)) = k7_subset_1(X0_44,X0_41,X1_41) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_583,plain,
% 7.58/1.50      ( k9_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41)) = k7_subset_1(X0_44,X0_41,X1_41)
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1269,plain,
% 7.58/1.50      ( k9_subset_1(X0_44,X0_41,k3_subset_1(X0_44,k3_subset_1(X0_44,X1_41))) = k7_subset_1(X0_44,X0_41,k3_subset_1(X0_44,X1_41))
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_580,c_583]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16776,plain,
% 7.58/1.50      ( k9_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK1))
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_1269]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_327,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_582,plain,
% 7.58/1.50      ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1059,plain,
% 7.58/1.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_582]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16864,plain,
% 7.58/1.50      ( k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1)
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_16776,c_1059]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_18734,plain,
% 7.58/1.50      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_16864]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27696,plain,
% 7.58/1.50      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_27598,c_18734]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_324,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(X0_44,k4_subset_1(X0_44,X0_41,X1_41)),k3_subset_1(X0_44,X0_41))
% 7.58/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_585,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(X0_44,k4_subset_1(X0_44,X0_41,X1_41)),k3_subset_1(X0_44,X0_41)) = iProver_top
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28064,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_27696,c_585]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1058,plain,
% 7.58/1.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_582]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28065,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,sK1))),sK2) = iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_28064,c_1058]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_0,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f26]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_330,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | k9_subset_1(X0_44,X0_41,X1_41) = k9_subset_1(X0_44,X1_41,X0_41) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_579,plain,
% 7.58/1.50      ( k9_subset_1(X0_44,X0_41,X1_41) = k9_subset_1(X0_44,X1_41,X0_41)
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1047,plain,
% 7.58/1.50      ( k9_subset_1(u1_struct_0(sK0),sK2,X0_41) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_579]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_328,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 7.58/1.50      | m1_subset_1(k9_subset_1(X0_44,X1_41,X0_41),k1_zfmisc_1(X0_44)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_581,plain,
% 7.58/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
% 7.58/1.50      | m1_subset_1(k9_subset_1(X0_44,X1_41,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1487,plain,
% 7.58/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1047,c_581]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_689,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_328]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_690,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2755,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_1487,c_15,c_690]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2762,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1047,c_2755]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3960,plain,
% 7.58/1.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK2,X0_41))) = k9_subset_1(u1_struct_0(sK0),sK2,X0_41) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2762,c_582]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28066,plain,
% 7.58/1.50      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK2) = iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_28065,c_3960]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25377,plain,
% 7.58/1.50      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_41),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_2366]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27230,plain,
% 7.58/1.50      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_25377]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16775,plain,
% 7.58/1.50      ( k9_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK2))
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_1269]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16869,plain,
% 7.58/1.50      ( k7_subset_1(u1_struct_0(sK0),X0_41,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2)
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_16775,c_1058]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_20623,plain,
% 7.58/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_16869]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27324,plain,
% 7.58/1.50      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_27230,c_20623]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27734,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_27324,c_585]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27735,plain,
% 7.58/1.50      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),sK1) = iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_27734,c_1059]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1048,plain,
% 7.58/1.50      ( k9_subset_1(u1_struct_0(sK0),sK1,X0_41) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_579]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1735,plain,
% 7.58/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1048,c_581]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14,plain,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_694,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_328]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_695,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3761,plain,
% 7.58/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_41,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_1735,c_14,c_695]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3781,plain,
% 7.58/1.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_41,sK1))) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3761,c_582]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4994,plain,
% 7.58/1.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,X0_41))) = k9_subset_1(u1_struct_0(sK0),X0_41,sK1) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1048,c_3781]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27736,plain,
% 7.58/1.50      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK1) = iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_27735,c_4994]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7,plain,
% 7.58/1.50      ( ~ v2_tex_2(X0,X1)
% 7.58/1.50      | v2_tex_2(X2,X1)
% 7.58/1.50      | ~ r1_tarski(X2,X0)
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.50      | ~ l1_pre_topc(X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_12,negated_conjecture,
% 7.58/1.50      ( l1_pre_topc(sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_148,plain,
% 7.58/1.50      ( ~ v2_tex_2(X0,X1)
% 7.58/1.50      | v2_tex_2(X2,X1)
% 7.58/1.50      | ~ r1_tarski(X2,X0)
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.50      | sK0 != X1 ),
% 7.58/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_149,plain,
% 7.58/1.50      ( ~ v2_tex_2(X0,sK0)
% 7.58/1.50      | v2_tex_2(X1,sK0)
% 7.58/1.50      | ~ r1_tarski(X1,X0)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(unflattening,[status(thm)],[c_148]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_319,plain,
% 7.58/1.50      ( ~ v2_tex_2(X0_41,sK0)
% 7.58/1.50      | v2_tex_2(X1_41,sK0)
% 7.58/1.50      | ~ r1_tarski(X1_41,X0_41)
% 7.58/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.58/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_149]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_590,plain,
% 7.58/1.50      ( v2_tex_2(X0_41,sK0) != iProver_top
% 7.58/1.50      | v2_tex_2(X1_41,sK0) = iProver_top
% 7.58/1.50      | r1_tarski(X1_41,X0_41) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_920,plain,
% 7.58/1.50      ( v2_tex_2(X0_41,sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK2,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(X0_41,sK2) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_588,c_590]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1167,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK2,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK2) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_581,c_920]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11602,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK2,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,X0_41),sK2) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1047,c_1167]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_12119,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK2,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK2) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_11602]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_921,plain,
% 7.58/1.50      ( v2_tex_2(X0_41,sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK1,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(X0_41,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_589,c_590]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1166,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK1,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_41,X1_41),sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_581,c_921]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9401,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK1,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,X0_41),sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1047,c_1166]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9766,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK1,sK0) != iProver_top
% 7.58/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_9401]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_680,plain,
% 7.58/1.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_329]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_681,plain,
% 7.58/1.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_677,plain,
% 7.58/1.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_329]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_678,plain,
% 7.58/1.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8,negated_conjecture,
% 7.58/1.50      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17,plain,
% 7.58/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9,negated_conjecture,
% 7.58/1.50      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16,plain,
% 7.58/1.50      ( v2_tex_2(sK2,sK0) = iProver_top
% 7.58/1.50      | v2_tex_2(sK1,sK0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(contradiction,plain,
% 7.58/1.50      ( $false ),
% 7.58/1.50      inference(minisat,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_28066,c_27736,c_12119,c_9766,c_681,c_678,c_17,c_16,
% 7.58/1.50                 c_15,c_14]) ).
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  ------                               Statistics
% 7.58/1.50  
% 7.58/1.50  ------ General
% 7.58/1.50  
% 7.58/1.50  abstr_ref_over_cycles:                  0
% 7.58/1.50  abstr_ref_under_cycles:                 0
% 7.58/1.50  gc_basic_clause_elim:                   0
% 7.58/1.50  forced_gc_time:                         0
% 7.58/1.50  parsing_time:                           0.009
% 7.58/1.50  unif_index_cands_time:                  0.
% 7.58/1.50  unif_index_add_time:                    0.
% 7.58/1.50  orderings_time:                         0.
% 7.58/1.50  out_proof_time:                         0.011
% 7.58/1.50  total_time:                             0.855
% 7.58/1.50  num_of_symbols:                         45
% 7.58/1.50  num_of_terms:                           30955
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing
% 7.58/1.50  
% 7.58/1.50  num_of_splits:                          0
% 7.58/1.50  num_of_split_atoms:                     0
% 7.58/1.50  num_of_reused_defs:                     0
% 7.58/1.50  num_eq_ax_congr_red:                    23
% 7.58/1.50  num_of_sem_filtered_clauses:            1
% 7.58/1.50  num_of_subtypes:                        4
% 7.58/1.50  monotx_restored_types:                  0
% 7.58/1.50  sat_num_of_epr_types:                   0
% 7.58/1.50  sat_num_of_non_cyclic_types:            0
% 7.58/1.50  sat_guarded_non_collapsed_types:        1
% 7.58/1.50  num_pure_diseq_elim:                    0
% 7.58/1.50  simp_replaced_by:                       0
% 7.58/1.50  res_preprocessed:                       66
% 7.58/1.50  prep_upred:                             0
% 7.58/1.50  prep_unflattend:                        5
% 7.58/1.50  smt_new_axioms:                         0
% 7.58/1.50  pred_elim_cands:                        3
% 7.58/1.50  pred_elim:                              1
% 7.58/1.50  pred_elim_cl:                           1
% 7.58/1.50  pred_elim_cycles:                       3
% 7.58/1.50  merged_defs:                            0
% 7.58/1.50  merged_defs_ncl:                        0
% 7.58/1.50  bin_hyper_res:                          0
% 7.58/1.50  prep_cycles:                            4
% 7.58/1.50  pred_elim_time:                         0.001
% 7.58/1.50  splitting_time:                         0.
% 7.58/1.50  sem_filter_time:                        0.
% 7.58/1.50  monotx_time:                            0.
% 7.58/1.50  subtype_inf_time:                       0.
% 7.58/1.50  
% 7.58/1.50  ------ Problem properties
% 7.58/1.50  
% 7.58/1.50  clauses:                                12
% 7.58/1.50  conjectures:                            4
% 7.58/1.50  epr:                                    1
% 7.58/1.50  horn:                                   11
% 7.58/1.50  ground:                                 4
% 7.58/1.50  unary:                                  3
% 7.58/1.50  binary:                                 5
% 7.58/1.50  lits:                                   27
% 7.58/1.50  lits_eq:                                4
% 7.58/1.50  fd_pure:                                0
% 7.58/1.50  fd_pseudo:                              0
% 7.58/1.50  fd_cond:                                0
% 7.58/1.50  fd_pseudo_cond:                         0
% 7.58/1.50  ac_symbols:                             0
% 7.58/1.50  
% 7.58/1.50  ------ Propositional Solver
% 7.58/1.50  
% 7.58/1.50  prop_solver_calls:                      29
% 7.58/1.50  prop_fast_solver_calls:                 611
% 7.58/1.50  smt_solver_calls:                       0
% 7.58/1.50  smt_fast_solver_calls:                  0
% 7.58/1.50  prop_num_of_clauses:                    8991
% 7.58/1.50  prop_preprocess_simplified:             13674
% 7.58/1.50  prop_fo_subsumed:                       6
% 7.58/1.50  prop_solver_time:                       0.
% 7.58/1.50  smt_solver_time:                        0.
% 7.58/1.50  smt_fast_solver_time:                   0.
% 7.58/1.50  prop_fast_solver_time:                  0.
% 7.58/1.50  prop_unsat_core_time:                   0.001
% 7.58/1.50  
% 7.58/1.50  ------ QBF
% 7.58/1.50  
% 7.58/1.50  qbf_q_res:                              0
% 7.58/1.50  qbf_num_tautologies:                    0
% 7.58/1.50  qbf_prep_cycles:                        0
% 7.58/1.50  
% 7.58/1.50  ------ BMC1
% 7.58/1.50  
% 7.58/1.50  bmc1_current_bound:                     -1
% 7.58/1.50  bmc1_last_solved_bound:                 -1
% 7.58/1.50  bmc1_unsat_core_size:                   -1
% 7.58/1.50  bmc1_unsat_core_parents_size:           -1
% 7.58/1.50  bmc1_merge_next_fun:                    0
% 7.58/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation
% 7.58/1.50  
% 7.58/1.50  inst_num_of_clauses:                    1974
% 7.58/1.50  inst_num_in_passive:                    782
% 7.58/1.50  inst_num_in_active:                     883
% 7.58/1.50  inst_num_in_unprocessed:                309
% 7.58/1.50  inst_num_of_loops:                      920
% 7.58/1.50  inst_num_of_learning_restarts:          0
% 7.58/1.50  inst_num_moves_active_passive:          35
% 7.58/1.50  inst_lit_activity:                      0
% 7.58/1.50  inst_lit_activity_moves:                0
% 7.58/1.50  inst_num_tautologies:                   0
% 7.58/1.50  inst_num_prop_implied:                  0
% 7.58/1.50  inst_num_existing_simplified:           0
% 7.58/1.50  inst_num_eq_res_simplified:             0
% 7.58/1.50  inst_num_child_elim:                    0
% 7.58/1.50  inst_num_of_dismatching_blockings:      2308
% 7.58/1.50  inst_num_of_non_proper_insts:           2122
% 7.58/1.50  inst_num_of_duplicates:                 0
% 7.58/1.50  inst_inst_num_from_inst_to_res:         0
% 7.58/1.50  inst_dismatching_checking_time:         0.
% 7.58/1.50  
% 7.58/1.50  ------ Resolution
% 7.58/1.50  
% 7.58/1.50  res_num_of_clauses:                     0
% 7.58/1.50  res_num_in_passive:                     0
% 7.58/1.50  res_num_in_active:                      0
% 7.58/1.50  res_num_of_loops:                       70
% 7.58/1.50  res_forward_subset_subsumed:            105
% 7.58/1.50  res_backward_subset_subsumed:           2
% 7.58/1.50  res_forward_subsumed:                   0
% 7.58/1.50  res_backward_subsumed:                  0
% 7.58/1.50  res_forward_subsumption_resolution:     0
% 7.58/1.50  res_backward_subsumption_resolution:    0
% 7.58/1.50  res_clause_to_clause_subsumption:       9309
% 7.58/1.50  res_orphan_elimination:                 0
% 7.58/1.50  res_tautology_del:                      443
% 7.58/1.50  res_num_eq_res_simplified:              0
% 7.58/1.50  res_num_sel_changes:                    0
% 7.58/1.50  res_moves_from_active_to_pass:          0
% 7.58/1.50  
% 7.58/1.50  ------ Superposition
% 7.58/1.50  
% 7.58/1.50  sup_time_total:                         0.
% 7.58/1.50  sup_time_generating:                    0.
% 7.58/1.50  sup_time_sim_full:                      0.
% 7.58/1.50  sup_time_sim_immed:                     0.
% 7.58/1.50  
% 7.58/1.50  sup_num_of_clauses:                     1551
% 7.58/1.50  sup_num_in_active:                      183
% 7.58/1.50  sup_num_in_passive:                     1368
% 7.58/1.50  sup_num_of_loops:                       182
% 7.58/1.50  sup_fw_superposition:                   2280
% 7.58/1.50  sup_bw_superposition:                   1817
% 7.58/1.50  sup_immediate_simplified:               1355
% 7.58/1.50  sup_given_eliminated:                   0
% 7.58/1.50  comparisons_done:                       0
% 7.58/1.50  comparisons_avoided:                    0
% 7.58/1.50  
% 7.58/1.50  ------ Simplifications
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  sim_fw_subset_subsumed:                 136
% 7.58/1.50  sim_bw_subset_subsumed:                 40
% 7.58/1.50  sim_fw_subsumed:                        416
% 7.58/1.50  sim_bw_subsumed:                        97
% 7.58/1.50  sim_fw_subsumption_res:                 0
% 7.58/1.50  sim_bw_subsumption_res:                 0
% 7.58/1.50  sim_tautology_del:                      4
% 7.58/1.50  sim_eq_tautology_del:                   64
% 7.58/1.50  sim_eq_res_simp:                        0
% 7.58/1.50  sim_fw_demodulated:                     148
% 7.58/1.50  sim_bw_demodulated:                     37
% 7.58/1.50  sim_light_normalised:                   554
% 7.58/1.50  sim_joinable_taut:                      0
% 7.58/1.50  sim_joinable_simp:                      0
% 7.58/1.50  sim_ac_normalised:                      0
% 7.58/1.50  sim_smt_subsumption:                    0
% 7.58/1.50  
%------------------------------------------------------------------------------
