%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1117+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:55 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 114 expanded)
%              Number of clauses        :   27 (  32 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 484 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK1(X0,X1,X2))
        & r1_tarski(X1,sK1(X0,X1,X2))
        & v4_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK1(X0,X1,X2))
                    & r1_tarski(X1,sK1(X0,X1,X2))
                    & v4_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_tarski(X1,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(sK3,k2_pre_topc(X0,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(sK2,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f20,f19])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,sK1(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ~ r1_tarski(sK3,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1054,plain,
    ( ~ r2_hidden(X0_43,X0_40)
    | r2_hidden(X0_43,X1_40)
    | ~ r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1133,plain,
    ( r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),X0_40)
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK3)
    | ~ r1_tarski(sK3,X0_40) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_1212,plain,
    ( r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK1(sK2,X0_40,sK0(sK3,k2_pre_topc(sK2,sK3))))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK3)
    | ~ r1_tarski(sK3,sK1(sK2,X0_40,sK0(sK3,k2_pre_topc(sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_1214,plain,
    ( r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK1(sK2,sK3,sK0(sK3,k2_pre_topc(sK2,sK3))))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK3)
    | ~ r1_tarski(sK3,sK1(sK2,sK3,sK0(sK3,k2_pre_topc(sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1052,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | r1_tarski(X0,sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2))
    | r1_tarski(X0,sK1(sK2,X0,X1)) ),
    inference(resolution,[status(thm)],[c_6,c_12])).

cnf(c_1046,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_43,k2_pre_topc(sK2,X0_40))
    | ~ r2_hidden(X0_43,u1_struct_0(sK2))
    | r1_tarski(X0_40,sK1(sK2,X0_40,X0_43)) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,X0_40))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),u1_struct_0(sK2))
    | r1_tarski(X0_40,sK1(sK2,X0_40,sK0(sK3,k2_pre_topc(sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),u1_struct_0(sK2))
    | r1_tarski(sK3,sK1(sK2,sK3,sK0(sK3,k2_pre_topc(sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,sK1(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,sK1(sK2,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_5,c_12])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_43,sK1(sK2,X0_40,X0_43))
    | r2_hidden(X0_43,k2_pre_topc(sK2,X0_40))
    | ~ r2_hidden(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_294])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK1(sK2,X0_40,sK0(sK3,k2_pre_topc(sK2,sK3))))
    | r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,X0_40))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK1(sK2,sK3,sK0(sK3,k2_pre_topc(sK2,sK3))))
    | r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_1137,plain,
    ( r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_448,plain,
    ( ~ r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_442,plain,
    ( r2_hidden(sK0(sK3,k2_pre_topc(sK2,sK3)),sK3) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1214,c_1171,c_1157,c_1153,c_1137,c_448,c_442,c_11])).


%------------------------------------------------------------------------------
