%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:10 EST 2020

% Result     : Theorem 23.52s
% Output     : CNFRefutation 23.52s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 576 expanded)
%              Number of clauses        :  104 ( 233 expanded)
%              Number of leaves         :   20 ( 123 expanded)
%              Depth                    :   19
%              Number of atoms          :  314 (1438 expanded)
%              Number of equality atoms :  145 ( 290 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(k3_tarski(X0_44),k3_tarski(X1_44)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_556,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(k3_tarski(X0_44),k3_tarski(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_4,plain,
    ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_226,plain,
    ( k2_xboole_0(k3_tarski(X0_44),k3_tarski(X1_44)) = k3_tarski(k2_xboole_0(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_229,plain,
    ( ~ r1_tarski(X0_44,k2_xboole_0(X1_44,X2_44))
    | r1_tarski(k4_xboole_0(X0_44,X1_44),X2_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_555,plain,
    ( r1_tarski(X0_44,k2_xboole_0(X1_44,X2_44)) != iProver_top
    | r1_tarski(k4_xboole_0(X0_44,X1_44),X2_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_868,plain,
    ( r1_tarski(X0_44,k3_tarski(k2_xboole_0(X1_44,X2_44))) != iProver_top
    | r1_tarski(k4_xboole_0(X0_44,k3_tarski(X1_44)),k3_tarski(X2_44)) = iProver_top ),
    inference(superposition,[status(thm)],[c_226,c_555])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_211,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_571,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X1_44)))
    | k5_setfam_1(X1_44,X0_44) = k3_tarski(X0_44) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_568,plain,
    ( k5_setfam_1(X0_44,X1_44) = k3_tarski(X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_934,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_571,c_568])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X1_44)))
    | m1_subset_1(k5_setfam_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_567,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X1_44))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_1400,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_567])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1694,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1400,c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k7_subset_1(X1_44,X0_44,X2_44) = k4_xboole_0(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_564,plain,
    ( k7_subset_1(X0_44,X1_44,X2_44) = k4_xboole_0(X1_44,X2_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1700,plain,
    ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0_44) = k4_xboole_0(k3_tarski(sK1),X0_44) ),
    inference(superposition,[status(thm)],[c_1694,c_564])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_212,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_570,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_933,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(superposition,[status(thm)],[c_570,c_568])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_213,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_569,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_998,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_933,c_569])).

cnf(c_999,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_998,c_934])).

cnf(c_991,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_44) = k4_xboole_0(sK1,X0_44) ),
    inference(superposition,[status(thm)],[c_571,c_564])).

cnf(c_1000,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_999,c_991])).

cnf(c_2873,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1700,c_1000])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k7_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_561,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k7_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_1336,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_561])).

cnf(c_3319,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_20])).

cnf(c_3326,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0_44)) = k3_tarski(k4_xboole_0(sK1,X0_44)) ),
    inference(superposition,[status(thm)],[c_3319,c_568])).

cnf(c_71603,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2873,c_3326])).

cnf(c_71605,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_71603])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_230,plain,
    ( k2_xboole_0(X0_44,k4_xboole_0(X1_44,X0_44)) = k2_xboole_0(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_71606,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_71605,c_230])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | k4_subset_1(X1_44,X2_44,X0_44) = k2_xboole_0(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_563,plain,
    ( k4_subset_1(X0_44,X1_44,X2_44) = k2_xboole_0(X1_44,X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1943,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,sK1) = k2_xboole_0(X0_44,sK1)
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_571,c_563])).

cnf(c_2392,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_570,c_1943])).

cnf(c_1942,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,sK2) = k2_xboole_0(X0_44,sK2)
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_563])).

cnf(c_2137,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_571,c_1942])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | k4_subset_1(X1_44,X0_44,X2_44) = k4_subset_1(X1_44,X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_557,plain,
    ( k4_subset_1(X0_44,X1_44,X2_44) = k4_subset_1(X0_44,X2_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_1213,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,X0_44) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,sK2)
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_557])).

cnf(c_1497,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_571,c_1213])).

cnf(c_2221,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2137,c_1497])).

cnf(c_2398,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2392,c_2221])).

cnf(c_71607,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_71606,c_2398])).

cnf(c_71610,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_556,c_71607])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k3_subset_1(X1_44,X0_44) = k4_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_558,plain,
    ( k3_subset_1(X0_44,X1_44) = k4_xboole_0(X0_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_799,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    inference(superposition,[status(thm)],[c_570,c_558])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_559,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1064,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_799,c_559])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4263,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X2_44,X0_44) = k3_xboole_0(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_565,plain,
    ( k9_subset_1(X0_44,X1_44,X2_44) = k3_xboole_0(X1_44,X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_4270,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_xboole_0(X0_44,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
    inference(superposition,[status(thm)],[c_4263,c_565])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k3_subset_1(X1_44,k3_subset_1(X1_44,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_562,plain,
    ( k3_subset_1(X0_44,k3_subset_1(X0_44,X1_44)) = X1_44
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_878,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_571,c_562])).

cnf(c_800,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_571,c_558])).

cnf(c_879,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_878,c_800])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | r1_tarski(k3_subset_1(X1_44,X2_44),k3_subset_1(X1_44,k9_subset_1(X1_44,X2_44,X0_44))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_566,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(X2_44,k1_zfmisc_1(X1_44)) != iProver_top
    | r1_tarski(k3_subset_1(X1_44,X2_44),k3_subset_1(X1_44,k9_subset_1(X1_44,X2_44,X0_44))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_1977,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),X0_44))) = iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_566])).

cnf(c_1152,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_559])).

cnf(c_53473,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),X0_44))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1977,c_20,c_1152])).

cnf(c_53485,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4270,c_53473])).

cnf(c_2,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_228,plain,
    ( k3_xboole_0(k4_xboole_0(X0_44,X1_44),k4_xboole_0(X0_44,X2_44)) = k4_xboole_0(X0_44,k2_xboole_0(X1_44,X2_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k4_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_560,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(X2_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k4_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_2222,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_560])).

cnf(c_5486,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2222,c_20,c_21])).

cnf(c_5499,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_5486,c_562])).

cnf(c_5500,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_5486,c_558])).

cnf(c_5512,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_5499,c_5500])).

cnf(c_53493,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_53485,c_228,c_5512])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71610,c_53493,c_1064,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.52/3.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.52/3.51  
% 23.52/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.52/3.51  
% 23.52/3.51  ------  iProver source info
% 23.52/3.51  
% 23.52/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.52/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.52/3.51  git: non_committed_changes: false
% 23.52/3.51  git: last_make_outside_of_git: false
% 23.52/3.51  
% 23.52/3.51  ------ 
% 23.52/3.51  
% 23.52/3.51  ------ Input Options
% 23.52/3.51  
% 23.52/3.51  --out_options                           all
% 23.52/3.51  --tptp_safe_out                         true
% 23.52/3.51  --problem_path                          ""
% 23.52/3.51  --include_path                          ""
% 23.52/3.51  --clausifier                            res/vclausify_rel
% 23.52/3.51  --clausifier_options                    ""
% 23.52/3.51  --stdin                                 false
% 23.52/3.51  --stats_out                             all
% 23.52/3.51  
% 23.52/3.51  ------ General Options
% 23.52/3.51  
% 23.52/3.51  --fof                                   false
% 23.52/3.51  --time_out_real                         305.
% 23.52/3.51  --time_out_virtual                      -1.
% 23.52/3.51  --symbol_type_check                     false
% 23.52/3.51  --clausify_out                          false
% 23.52/3.51  --sig_cnt_out                           false
% 23.52/3.51  --trig_cnt_out                          false
% 23.52/3.51  --trig_cnt_out_tolerance                1.
% 23.52/3.51  --trig_cnt_out_sk_spl                   false
% 23.52/3.51  --abstr_cl_out                          false
% 23.52/3.51  
% 23.52/3.51  ------ Global Options
% 23.52/3.51  
% 23.52/3.51  --schedule                              default
% 23.52/3.51  --add_important_lit                     false
% 23.52/3.51  --prop_solver_per_cl                    1000
% 23.52/3.51  --min_unsat_core                        false
% 23.52/3.51  --soft_assumptions                      false
% 23.52/3.51  --soft_lemma_size                       3
% 23.52/3.51  --prop_impl_unit_size                   0
% 23.52/3.51  --prop_impl_unit                        []
% 23.52/3.51  --share_sel_clauses                     true
% 23.52/3.51  --reset_solvers                         false
% 23.52/3.51  --bc_imp_inh                            [conj_cone]
% 23.52/3.51  --conj_cone_tolerance                   3.
% 23.52/3.51  --extra_neg_conj                        none
% 23.52/3.51  --large_theory_mode                     true
% 23.52/3.51  --prolific_symb_bound                   200
% 23.52/3.51  --lt_threshold                          2000
% 23.52/3.51  --clause_weak_htbl                      true
% 23.52/3.51  --gc_record_bc_elim                     false
% 23.52/3.51  
% 23.52/3.51  ------ Preprocessing Options
% 23.52/3.51  
% 23.52/3.51  --preprocessing_flag                    true
% 23.52/3.51  --time_out_prep_mult                    0.1
% 23.52/3.51  --splitting_mode                        input
% 23.52/3.51  --splitting_grd                         true
% 23.52/3.51  --splitting_cvd                         false
% 23.52/3.51  --splitting_cvd_svl                     false
% 23.52/3.51  --splitting_nvd                         32
% 23.52/3.51  --sub_typing                            true
% 23.52/3.51  --prep_gs_sim                           true
% 23.52/3.51  --prep_unflatten                        true
% 23.52/3.51  --prep_res_sim                          true
% 23.52/3.51  --prep_upred                            true
% 23.52/3.51  --prep_sem_filter                       exhaustive
% 23.52/3.51  --prep_sem_filter_out                   false
% 23.52/3.51  --pred_elim                             true
% 23.52/3.51  --res_sim_input                         true
% 23.52/3.51  --eq_ax_congr_red                       true
% 23.52/3.51  --pure_diseq_elim                       true
% 23.52/3.51  --brand_transform                       false
% 23.52/3.51  --non_eq_to_eq                          false
% 23.52/3.51  --prep_def_merge                        true
% 23.52/3.51  --prep_def_merge_prop_impl              false
% 23.52/3.51  --prep_def_merge_mbd                    true
% 23.52/3.51  --prep_def_merge_tr_red                 false
% 23.52/3.51  --prep_def_merge_tr_cl                  false
% 23.52/3.51  --smt_preprocessing                     true
% 23.52/3.51  --smt_ac_axioms                         fast
% 23.52/3.51  --preprocessed_out                      false
% 23.52/3.51  --preprocessed_stats                    false
% 23.52/3.51  
% 23.52/3.51  ------ Abstraction refinement Options
% 23.52/3.51  
% 23.52/3.51  --abstr_ref                             []
% 23.52/3.51  --abstr_ref_prep                        false
% 23.52/3.51  --abstr_ref_until_sat                   false
% 23.52/3.51  --abstr_ref_sig_restrict                funpre
% 23.52/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.52/3.51  --abstr_ref_under                       []
% 23.52/3.51  
% 23.52/3.51  ------ SAT Options
% 23.52/3.51  
% 23.52/3.51  --sat_mode                              false
% 23.52/3.51  --sat_fm_restart_options                ""
% 23.52/3.51  --sat_gr_def                            false
% 23.52/3.51  --sat_epr_types                         true
% 23.52/3.51  --sat_non_cyclic_types                  false
% 23.52/3.51  --sat_finite_models                     false
% 23.52/3.51  --sat_fm_lemmas                         false
% 23.52/3.51  --sat_fm_prep                           false
% 23.52/3.51  --sat_fm_uc_incr                        true
% 23.52/3.51  --sat_out_model                         small
% 23.52/3.51  --sat_out_clauses                       false
% 23.52/3.51  
% 23.52/3.51  ------ QBF Options
% 23.52/3.51  
% 23.52/3.51  --qbf_mode                              false
% 23.52/3.51  --qbf_elim_univ                         false
% 23.52/3.51  --qbf_dom_inst                          none
% 23.52/3.51  --qbf_dom_pre_inst                      false
% 23.52/3.51  --qbf_sk_in                             false
% 23.52/3.51  --qbf_pred_elim                         true
% 23.52/3.51  --qbf_split                             512
% 23.52/3.51  
% 23.52/3.51  ------ BMC1 Options
% 23.52/3.51  
% 23.52/3.51  --bmc1_incremental                      false
% 23.52/3.51  --bmc1_axioms                           reachable_all
% 23.52/3.51  --bmc1_min_bound                        0
% 23.52/3.51  --bmc1_max_bound                        -1
% 23.52/3.51  --bmc1_max_bound_default                -1
% 23.52/3.51  --bmc1_symbol_reachability              true
% 23.52/3.51  --bmc1_property_lemmas                  false
% 23.52/3.51  --bmc1_k_induction                      false
% 23.52/3.51  --bmc1_non_equiv_states                 false
% 23.52/3.51  --bmc1_deadlock                         false
% 23.52/3.51  --bmc1_ucm                              false
% 23.52/3.51  --bmc1_add_unsat_core                   none
% 23.52/3.51  --bmc1_unsat_core_children              false
% 23.52/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.52/3.51  --bmc1_out_stat                         full
% 23.52/3.51  --bmc1_ground_init                      false
% 23.52/3.51  --bmc1_pre_inst_next_state              false
% 23.52/3.51  --bmc1_pre_inst_state                   false
% 23.52/3.51  --bmc1_pre_inst_reach_state             false
% 23.52/3.51  --bmc1_out_unsat_core                   false
% 23.52/3.51  --bmc1_aig_witness_out                  false
% 23.52/3.51  --bmc1_verbose                          false
% 23.52/3.51  --bmc1_dump_clauses_tptp                false
% 23.52/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.52/3.51  --bmc1_dump_file                        -
% 23.52/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.52/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.52/3.51  --bmc1_ucm_extend_mode                  1
% 23.52/3.51  --bmc1_ucm_init_mode                    2
% 23.52/3.51  --bmc1_ucm_cone_mode                    none
% 23.52/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.52/3.51  --bmc1_ucm_relax_model                  4
% 23.52/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.52/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.52/3.51  --bmc1_ucm_layered_model                none
% 23.52/3.51  --bmc1_ucm_max_lemma_size               10
% 23.52/3.51  
% 23.52/3.51  ------ AIG Options
% 23.52/3.51  
% 23.52/3.51  --aig_mode                              false
% 23.52/3.51  
% 23.52/3.51  ------ Instantiation Options
% 23.52/3.51  
% 23.52/3.51  --instantiation_flag                    true
% 23.52/3.51  --inst_sos_flag                         true
% 23.52/3.51  --inst_sos_phase                        true
% 23.52/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.52/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.52/3.51  --inst_lit_sel_side                     num_symb
% 23.52/3.51  --inst_solver_per_active                1400
% 23.52/3.51  --inst_solver_calls_frac                1.
% 23.52/3.51  --inst_passive_queue_type               priority_queues
% 23.52/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.52/3.51  --inst_passive_queues_freq              [25;2]
% 23.52/3.51  --inst_dismatching                      true
% 23.52/3.51  --inst_eager_unprocessed_to_passive     true
% 23.52/3.51  --inst_prop_sim_given                   true
% 23.52/3.51  --inst_prop_sim_new                     false
% 23.52/3.51  --inst_subs_new                         false
% 23.52/3.51  --inst_eq_res_simp                      false
% 23.52/3.51  --inst_subs_given                       false
% 23.52/3.51  --inst_orphan_elimination               true
% 23.52/3.51  --inst_learning_loop_flag               true
% 23.52/3.51  --inst_learning_start                   3000
% 23.52/3.51  --inst_learning_factor                  2
% 23.52/3.51  --inst_start_prop_sim_after_learn       3
% 23.52/3.51  --inst_sel_renew                        solver
% 23.52/3.51  --inst_lit_activity_flag                true
% 23.52/3.51  --inst_restr_to_given                   false
% 23.52/3.51  --inst_activity_threshold               500
% 23.52/3.51  --inst_out_proof                        true
% 23.52/3.51  
% 23.52/3.51  ------ Resolution Options
% 23.52/3.51  
% 23.52/3.51  --resolution_flag                       true
% 23.52/3.51  --res_lit_sel                           adaptive
% 23.52/3.51  --res_lit_sel_side                      none
% 23.52/3.51  --res_ordering                          kbo
% 23.52/3.51  --res_to_prop_solver                    active
% 23.52/3.51  --res_prop_simpl_new                    false
% 23.52/3.51  --res_prop_simpl_given                  true
% 23.52/3.51  --res_passive_queue_type                priority_queues
% 23.52/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.52/3.51  --res_passive_queues_freq               [15;5]
% 23.52/3.51  --res_forward_subs                      full
% 23.52/3.51  --res_backward_subs                     full
% 23.52/3.51  --res_forward_subs_resolution           true
% 23.52/3.51  --res_backward_subs_resolution          true
% 23.52/3.51  --res_orphan_elimination                true
% 23.52/3.51  --res_time_limit                        2.
% 23.52/3.51  --res_out_proof                         true
% 23.52/3.51  
% 23.52/3.51  ------ Superposition Options
% 23.52/3.51  
% 23.52/3.51  --superposition_flag                    true
% 23.52/3.51  --sup_passive_queue_type                priority_queues
% 23.52/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.52/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.52/3.51  --demod_completeness_check              fast
% 23.52/3.51  --demod_use_ground                      true
% 23.52/3.51  --sup_to_prop_solver                    passive
% 23.52/3.51  --sup_prop_simpl_new                    true
% 23.52/3.51  --sup_prop_simpl_given                  true
% 23.52/3.51  --sup_fun_splitting                     true
% 23.52/3.51  --sup_smt_interval                      50000
% 23.52/3.51  
% 23.52/3.51  ------ Superposition Simplification Setup
% 23.52/3.51  
% 23.52/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.52/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.52/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.52/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.52/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.52/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.52/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.52/3.51  --sup_immed_triv                        [TrivRules]
% 23.52/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.52/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.52/3.51  --sup_immed_bw_main                     []
% 23.52/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.52/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.52/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.52/3.51  --sup_input_bw                          []
% 23.52/3.51  
% 23.52/3.51  ------ Combination Options
% 23.52/3.51  
% 23.52/3.51  --comb_res_mult                         3
% 23.52/3.51  --comb_sup_mult                         2
% 23.52/3.51  --comb_inst_mult                        10
% 23.52/3.51  
% 23.52/3.51  ------ Debug Options
% 23.52/3.51  
% 23.52/3.51  --dbg_backtrace                         false
% 23.52/3.51  --dbg_dump_prop_clauses                 false
% 23.52/3.51  --dbg_dump_prop_clauses_file            -
% 23.52/3.51  --dbg_out_stat                          false
% 23.52/3.51  ------ Parsing...
% 23.52/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.52/3.51  
% 23.52/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.52/3.51  
% 23.52/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.52/3.51  
% 23.52/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.52/3.51  ------ Proving...
% 23.52/3.51  ------ Problem Properties 
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  clauses                                 20
% 23.52/3.51  conjectures                             3
% 23.52/3.51  EPR                                     0
% 23.52/3.51  Horn                                    20
% 23.52/3.51  unary                                   6
% 23.52/3.51  binary                                  10
% 23.52/3.51  lits                                    38
% 23.52/3.51  lits eq                                 10
% 23.52/3.51  fd_pure                                 0
% 23.52/3.51  fd_pseudo                               0
% 23.52/3.51  fd_cond                                 0
% 23.52/3.51  fd_pseudo_cond                          0
% 23.52/3.51  AC symbols                              0
% 23.52/3.51  
% 23.52/3.51  ------ Schedule dynamic 5 is on 
% 23.52/3.51  
% 23.52/3.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  ------ 
% 23.52/3.51  Current options:
% 23.52/3.51  ------ 
% 23.52/3.51  
% 23.52/3.51  ------ Input Options
% 23.52/3.51  
% 23.52/3.51  --out_options                           all
% 23.52/3.51  --tptp_safe_out                         true
% 23.52/3.51  --problem_path                          ""
% 23.52/3.51  --include_path                          ""
% 23.52/3.51  --clausifier                            res/vclausify_rel
% 23.52/3.51  --clausifier_options                    ""
% 23.52/3.51  --stdin                                 false
% 23.52/3.51  --stats_out                             all
% 23.52/3.51  
% 23.52/3.51  ------ General Options
% 23.52/3.51  
% 23.52/3.51  --fof                                   false
% 23.52/3.51  --time_out_real                         305.
% 23.52/3.51  --time_out_virtual                      -1.
% 23.52/3.51  --symbol_type_check                     false
% 23.52/3.51  --clausify_out                          false
% 23.52/3.51  --sig_cnt_out                           false
% 23.52/3.51  --trig_cnt_out                          false
% 23.52/3.51  --trig_cnt_out_tolerance                1.
% 23.52/3.51  --trig_cnt_out_sk_spl                   false
% 23.52/3.51  --abstr_cl_out                          false
% 23.52/3.51  
% 23.52/3.51  ------ Global Options
% 23.52/3.51  
% 23.52/3.51  --schedule                              default
% 23.52/3.51  --add_important_lit                     false
% 23.52/3.51  --prop_solver_per_cl                    1000
% 23.52/3.51  --min_unsat_core                        false
% 23.52/3.51  --soft_assumptions                      false
% 23.52/3.51  --soft_lemma_size                       3
% 23.52/3.51  --prop_impl_unit_size                   0
% 23.52/3.51  --prop_impl_unit                        []
% 23.52/3.51  --share_sel_clauses                     true
% 23.52/3.51  --reset_solvers                         false
% 23.52/3.51  --bc_imp_inh                            [conj_cone]
% 23.52/3.51  --conj_cone_tolerance                   3.
% 23.52/3.51  --extra_neg_conj                        none
% 23.52/3.51  --large_theory_mode                     true
% 23.52/3.51  --prolific_symb_bound                   200
% 23.52/3.51  --lt_threshold                          2000
% 23.52/3.51  --clause_weak_htbl                      true
% 23.52/3.51  --gc_record_bc_elim                     false
% 23.52/3.51  
% 23.52/3.51  ------ Preprocessing Options
% 23.52/3.51  
% 23.52/3.51  --preprocessing_flag                    true
% 23.52/3.51  --time_out_prep_mult                    0.1
% 23.52/3.51  --splitting_mode                        input
% 23.52/3.51  --splitting_grd                         true
% 23.52/3.51  --splitting_cvd                         false
% 23.52/3.51  --splitting_cvd_svl                     false
% 23.52/3.51  --splitting_nvd                         32
% 23.52/3.51  --sub_typing                            true
% 23.52/3.51  --prep_gs_sim                           true
% 23.52/3.51  --prep_unflatten                        true
% 23.52/3.51  --prep_res_sim                          true
% 23.52/3.51  --prep_upred                            true
% 23.52/3.51  --prep_sem_filter                       exhaustive
% 23.52/3.51  --prep_sem_filter_out                   false
% 23.52/3.51  --pred_elim                             true
% 23.52/3.51  --res_sim_input                         true
% 23.52/3.51  --eq_ax_congr_red                       true
% 23.52/3.51  --pure_diseq_elim                       true
% 23.52/3.51  --brand_transform                       false
% 23.52/3.51  --non_eq_to_eq                          false
% 23.52/3.51  --prep_def_merge                        true
% 23.52/3.51  --prep_def_merge_prop_impl              false
% 23.52/3.51  --prep_def_merge_mbd                    true
% 23.52/3.51  --prep_def_merge_tr_red                 false
% 23.52/3.51  --prep_def_merge_tr_cl                  false
% 23.52/3.51  --smt_preprocessing                     true
% 23.52/3.51  --smt_ac_axioms                         fast
% 23.52/3.51  --preprocessed_out                      false
% 23.52/3.51  --preprocessed_stats                    false
% 23.52/3.51  
% 23.52/3.51  ------ Abstraction refinement Options
% 23.52/3.51  
% 23.52/3.51  --abstr_ref                             []
% 23.52/3.51  --abstr_ref_prep                        false
% 23.52/3.51  --abstr_ref_until_sat                   false
% 23.52/3.51  --abstr_ref_sig_restrict                funpre
% 23.52/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.52/3.51  --abstr_ref_under                       []
% 23.52/3.51  
% 23.52/3.51  ------ SAT Options
% 23.52/3.51  
% 23.52/3.51  --sat_mode                              false
% 23.52/3.51  --sat_fm_restart_options                ""
% 23.52/3.51  --sat_gr_def                            false
% 23.52/3.51  --sat_epr_types                         true
% 23.52/3.51  --sat_non_cyclic_types                  false
% 23.52/3.51  --sat_finite_models                     false
% 23.52/3.51  --sat_fm_lemmas                         false
% 23.52/3.51  --sat_fm_prep                           false
% 23.52/3.51  --sat_fm_uc_incr                        true
% 23.52/3.51  --sat_out_model                         small
% 23.52/3.51  --sat_out_clauses                       false
% 23.52/3.51  
% 23.52/3.51  ------ QBF Options
% 23.52/3.51  
% 23.52/3.51  --qbf_mode                              false
% 23.52/3.51  --qbf_elim_univ                         false
% 23.52/3.51  --qbf_dom_inst                          none
% 23.52/3.51  --qbf_dom_pre_inst                      false
% 23.52/3.51  --qbf_sk_in                             false
% 23.52/3.51  --qbf_pred_elim                         true
% 23.52/3.51  --qbf_split                             512
% 23.52/3.51  
% 23.52/3.51  ------ BMC1 Options
% 23.52/3.51  
% 23.52/3.51  --bmc1_incremental                      false
% 23.52/3.51  --bmc1_axioms                           reachable_all
% 23.52/3.51  --bmc1_min_bound                        0
% 23.52/3.51  --bmc1_max_bound                        -1
% 23.52/3.51  --bmc1_max_bound_default                -1
% 23.52/3.51  --bmc1_symbol_reachability              true
% 23.52/3.51  --bmc1_property_lemmas                  false
% 23.52/3.51  --bmc1_k_induction                      false
% 23.52/3.51  --bmc1_non_equiv_states                 false
% 23.52/3.51  --bmc1_deadlock                         false
% 23.52/3.51  --bmc1_ucm                              false
% 23.52/3.51  --bmc1_add_unsat_core                   none
% 23.52/3.51  --bmc1_unsat_core_children              false
% 23.52/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.52/3.51  --bmc1_out_stat                         full
% 23.52/3.51  --bmc1_ground_init                      false
% 23.52/3.51  --bmc1_pre_inst_next_state              false
% 23.52/3.51  --bmc1_pre_inst_state                   false
% 23.52/3.51  --bmc1_pre_inst_reach_state             false
% 23.52/3.51  --bmc1_out_unsat_core                   false
% 23.52/3.51  --bmc1_aig_witness_out                  false
% 23.52/3.51  --bmc1_verbose                          false
% 23.52/3.51  --bmc1_dump_clauses_tptp                false
% 23.52/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.52/3.51  --bmc1_dump_file                        -
% 23.52/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.52/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.52/3.51  --bmc1_ucm_extend_mode                  1
% 23.52/3.51  --bmc1_ucm_init_mode                    2
% 23.52/3.51  --bmc1_ucm_cone_mode                    none
% 23.52/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.52/3.51  --bmc1_ucm_relax_model                  4
% 23.52/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.52/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.52/3.51  --bmc1_ucm_layered_model                none
% 23.52/3.51  --bmc1_ucm_max_lemma_size               10
% 23.52/3.51  
% 23.52/3.51  ------ AIG Options
% 23.52/3.51  
% 23.52/3.51  --aig_mode                              false
% 23.52/3.51  
% 23.52/3.51  ------ Instantiation Options
% 23.52/3.51  
% 23.52/3.51  --instantiation_flag                    true
% 23.52/3.51  --inst_sos_flag                         true
% 23.52/3.51  --inst_sos_phase                        true
% 23.52/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.52/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.52/3.51  --inst_lit_sel_side                     none
% 23.52/3.51  --inst_solver_per_active                1400
% 23.52/3.51  --inst_solver_calls_frac                1.
% 23.52/3.51  --inst_passive_queue_type               priority_queues
% 23.52/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.52/3.51  --inst_passive_queues_freq              [25;2]
% 23.52/3.51  --inst_dismatching                      true
% 23.52/3.51  --inst_eager_unprocessed_to_passive     true
% 23.52/3.51  --inst_prop_sim_given                   true
% 23.52/3.51  --inst_prop_sim_new                     false
% 23.52/3.51  --inst_subs_new                         false
% 23.52/3.51  --inst_eq_res_simp                      false
% 23.52/3.51  --inst_subs_given                       false
% 23.52/3.51  --inst_orphan_elimination               true
% 23.52/3.51  --inst_learning_loop_flag               true
% 23.52/3.51  --inst_learning_start                   3000
% 23.52/3.51  --inst_learning_factor                  2
% 23.52/3.51  --inst_start_prop_sim_after_learn       3
% 23.52/3.51  --inst_sel_renew                        solver
% 23.52/3.51  --inst_lit_activity_flag                true
% 23.52/3.51  --inst_restr_to_given                   false
% 23.52/3.51  --inst_activity_threshold               500
% 23.52/3.51  --inst_out_proof                        true
% 23.52/3.51  
% 23.52/3.51  ------ Resolution Options
% 23.52/3.51  
% 23.52/3.51  --resolution_flag                       false
% 23.52/3.51  --res_lit_sel                           adaptive
% 23.52/3.51  --res_lit_sel_side                      none
% 23.52/3.51  --res_ordering                          kbo
% 23.52/3.51  --res_to_prop_solver                    active
% 23.52/3.51  --res_prop_simpl_new                    false
% 23.52/3.51  --res_prop_simpl_given                  true
% 23.52/3.51  --res_passive_queue_type                priority_queues
% 23.52/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.52/3.51  --res_passive_queues_freq               [15;5]
% 23.52/3.51  --res_forward_subs                      full
% 23.52/3.51  --res_backward_subs                     full
% 23.52/3.51  --res_forward_subs_resolution           true
% 23.52/3.51  --res_backward_subs_resolution          true
% 23.52/3.51  --res_orphan_elimination                true
% 23.52/3.51  --res_time_limit                        2.
% 23.52/3.51  --res_out_proof                         true
% 23.52/3.51  
% 23.52/3.51  ------ Superposition Options
% 23.52/3.51  
% 23.52/3.51  --superposition_flag                    true
% 23.52/3.51  --sup_passive_queue_type                priority_queues
% 23.52/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.52/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.52/3.51  --demod_completeness_check              fast
% 23.52/3.51  --demod_use_ground                      true
% 23.52/3.51  --sup_to_prop_solver                    passive
% 23.52/3.51  --sup_prop_simpl_new                    true
% 23.52/3.51  --sup_prop_simpl_given                  true
% 23.52/3.51  --sup_fun_splitting                     true
% 23.52/3.51  --sup_smt_interval                      50000
% 23.52/3.51  
% 23.52/3.51  ------ Superposition Simplification Setup
% 23.52/3.51  
% 23.52/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.52/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.52/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.52/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.52/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.52/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.52/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.52/3.51  --sup_immed_triv                        [TrivRules]
% 23.52/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.52/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.52/3.51  --sup_immed_bw_main                     []
% 23.52/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.52/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.52/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.52/3.51  --sup_input_bw                          []
% 23.52/3.51  
% 23.52/3.51  ------ Combination Options
% 23.52/3.51  
% 23.52/3.51  --comb_res_mult                         3
% 23.52/3.51  --comb_sup_mult                         2
% 23.52/3.51  --comb_inst_mult                        10
% 23.52/3.51  
% 23.52/3.51  ------ Debug Options
% 23.52/3.51  
% 23.52/3.51  --dbg_backtrace                         false
% 23.52/3.51  --dbg_dump_prop_clauses                 false
% 23.52/3.51  --dbg_dump_prop_clauses_file            -
% 23.52/3.51  --dbg_out_stat                          false
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  ------ Proving...
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  % SZS status Theorem for theBenchmark.p
% 23.52/3.51  
% 23.52/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.52/3.51  
% 23.52/3.51  fof(f4,axiom,(
% 23.52/3.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f22,plain,(
% 23.52/3.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 23.52/3.51    inference(ennf_transformation,[],[f4])).
% 23.52/3.51  
% 23.52/3.51  fof(f45,plain,(
% 23.52/3.51    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 23.52/3.51    inference(cnf_transformation,[],[f22])).
% 23.52/3.51  
% 23.52/3.51  fof(f5,axiom,(
% 23.52/3.51    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f46,plain,(
% 23.52/3.51    ( ! [X0,X1] : (k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f5])).
% 23.52/3.51  
% 23.52/3.51  fof(f2,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f21,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.52/3.51    inference(ennf_transformation,[],[f2])).
% 23.52/3.51  
% 23.52/3.51  fof(f43,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f21])).
% 23.52/3.51  
% 23.52/3.51  fof(f18,conjecture,(
% 23.52/3.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f19,negated_conjecture,(
% 23.52/3.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 23.52/3.51    inference(negated_conjecture,[],[f18])).
% 23.52/3.51  
% 23.52/3.51  fof(f20,plain,(
% 23.52/3.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))))),
% 23.52/3.51    inference(pure_predicate_removal,[],[f19])).
% 23.52/3.51  
% 23.52/3.51  fof(f38,plain,(
% 23.52/3.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.52/3.51    inference(ennf_transformation,[],[f20])).
% 23.52/3.51  
% 23.52/3.51  fof(f40,plain,(
% 23.52/3.51    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 23.52/3.51    introduced(choice_axiom,[])).
% 23.52/3.51  
% 23.52/3.51  fof(f39,plain,(
% 23.52/3.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 23.52/3.51    introduced(choice_axiom,[])).
% 23.52/3.51  
% 23.52/3.51  fof(f41,plain,(
% 23.52/3.51    (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 23.52/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).
% 23.52/3.51  
% 23.52/3.51  fof(f59,plain,(
% 23.52/3.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 23.52/3.51    inference(cnf_transformation,[],[f41])).
% 23.52/3.51  
% 23.52/3.51  fof(f17,axiom,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f37,plain,(
% 23.52/3.51    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 23.52/3.51    inference(ennf_transformation,[],[f17])).
% 23.52/3.51  
% 23.52/3.51  fof(f58,plain,(
% 23.52/3.51    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f37])).
% 23.52/3.51  
% 23.52/3.51  fof(f16,axiom,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f36,plain,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 23.52/3.51    inference(ennf_transformation,[],[f16])).
% 23.52/3.51  
% 23.52/3.51  fof(f57,plain,(
% 23.52/3.51    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f36])).
% 23.52/3.51  
% 23.52/3.51  fof(f13,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f33,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f13])).
% 23.52/3.51  
% 23.52/3.51  fof(f54,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f33])).
% 23.52/3.51  
% 23.52/3.51  fof(f60,plain,(
% 23.52/3.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 23.52/3.51    inference(cnf_transformation,[],[f41])).
% 23.52/3.51  
% 23.52/3.51  fof(f61,plain,(
% 23.52/3.51    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 23.52/3.51    inference(cnf_transformation,[],[f41])).
% 23.52/3.51  
% 23.52/3.51  fof(f10,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f29,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f10])).
% 23.52/3.51  
% 23.52/3.51  fof(f51,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f29])).
% 23.52/3.51  
% 23.52/3.51  fof(f1,axiom,(
% 23.52/3.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f42,plain,(
% 23.52/3.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f1])).
% 23.52/3.51  
% 23.52/3.51  fof(f12,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f31,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.52/3.51    inference(ennf_transformation,[],[f12])).
% 23.52/3.51  
% 23.52/3.51  fof(f32,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(flattening,[],[f31])).
% 23.52/3.51  
% 23.52/3.51  fof(f53,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f32])).
% 23.52/3.51  
% 23.52/3.51  fof(f6,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f23,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.52/3.51    inference(ennf_transformation,[],[f6])).
% 23.52/3.51  
% 23.52/3.51  fof(f24,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(flattening,[],[f23])).
% 23.52/3.51  
% 23.52/3.51  fof(f47,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f24])).
% 23.52/3.51  
% 23.52/3.51  fof(f7,axiom,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f25,plain,(
% 23.52/3.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f7])).
% 23.52/3.51  
% 23.52/3.51  fof(f48,plain,(
% 23.52/3.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f25])).
% 23.52/3.51  
% 23.52/3.51  fof(f8,axiom,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f26,plain,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f8])).
% 23.52/3.51  
% 23.52/3.51  fof(f49,plain,(
% 23.52/3.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f26])).
% 23.52/3.51  
% 23.52/3.51  fof(f14,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f34,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f14])).
% 23.52/3.51  
% 23.52/3.51  fof(f55,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f34])).
% 23.52/3.51  
% 23.52/3.51  fof(f11,axiom,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f30,plain,(
% 23.52/3.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f11])).
% 23.52/3.51  
% 23.52/3.51  fof(f52,plain,(
% 23.52/3.51    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f30])).
% 23.52/3.51  
% 23.52/3.51  fof(f15,axiom,(
% 23.52/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f35,plain,(
% 23.52/3.51    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(ennf_transformation,[],[f15])).
% 23.52/3.51  
% 23.52/3.51  fof(f56,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f35])).
% 23.52/3.51  
% 23.52/3.51  fof(f3,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f44,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f3])).
% 23.52/3.51  
% 23.52/3.51  fof(f9,axiom,(
% 23.52/3.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 23.52/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.52/3.51  
% 23.52/3.51  fof(f27,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.52/3.51    inference(ennf_transformation,[],[f9])).
% 23.52/3.51  
% 23.52/3.51  fof(f28,plain,(
% 23.52/3.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.52/3.51    inference(flattening,[],[f27])).
% 23.52/3.51  
% 23.52/3.51  fof(f50,plain,(
% 23.52/3.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.52/3.51    inference(cnf_transformation,[],[f28])).
% 23.52/3.51  
% 23.52/3.51  cnf(c_3,plain,
% 23.52/3.51      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f45]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_227,plain,
% 23.52/3.51      ( ~ r1_tarski(X0_44,X1_44)
% 23.52/3.51      | r1_tarski(k3_tarski(X0_44),k3_tarski(X1_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_3]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_556,plain,
% 23.52/3.51      ( r1_tarski(X0_44,X1_44) != iProver_top
% 23.52/3.51      | r1_tarski(k3_tarski(X0_44),k3_tarski(X1_44)) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_4,plain,
% 23.52/3.51      ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f46]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_226,plain,
% 23.52/3.51      ( k2_xboole_0(k3_tarski(X0_44),k3_tarski(X1_44)) = k3_tarski(k2_xboole_0(X0_44,X1_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_4]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1,plain,
% 23.52/3.51      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.52/3.51      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 23.52/3.51      inference(cnf_transformation,[],[f43]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_229,plain,
% 23.52/3.51      ( ~ r1_tarski(X0_44,k2_xboole_0(X1_44,X2_44))
% 23.52/3.51      | r1_tarski(k4_xboole_0(X0_44,X1_44),X2_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_1]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_555,plain,
% 23.52/3.51      ( r1_tarski(X0_44,k2_xboole_0(X1_44,X2_44)) != iProver_top
% 23.52/3.51      | r1_tarski(k4_xboole_0(X0_44,X1_44),X2_44) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_868,plain,
% 23.52/3.51      ( r1_tarski(X0_44,k3_tarski(k2_xboole_0(X1_44,X2_44))) != iProver_top
% 23.52/3.51      | r1_tarski(k4_xboole_0(X0_44,k3_tarski(X1_44)),k3_tarski(X2_44)) = iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_226,c_555]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_19,negated_conjecture,
% 23.52/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 23.52/3.51      inference(cnf_transformation,[],[f59]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_211,negated_conjecture,
% 23.52/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_19]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_571,plain,
% 23.52/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_16,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 23.52/3.51      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 23.52/3.51      inference(cnf_transformation,[],[f58]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_214,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X1_44)))
% 23.52/3.51      | k5_setfam_1(X1_44,X0_44) = k3_tarski(X0_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_16]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_568,plain,
% 23.52/3.51      ( k5_setfam_1(X0_44,X1_44) = k3_tarski(X1_44)
% 23.52/3.51      | m1_subset_1(X1_44,k1_zfmisc_1(k1_zfmisc_1(X0_44))) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_934,plain,
% 23.52/3.51      ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_568]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_15,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 23.52/3.51      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f57]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_215,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X1_44)))
% 23.52/3.51      | m1_subset_1(k5_setfam_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_15]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_567,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(X1_44))) != iProver_top
% 23.52/3.51      | m1_subset_1(k5_setfam_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1400,plain,
% 23.52/3.51      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 23.52/3.51      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_934,c_567]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_20,plain,
% 23.52/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1694,plain,
% 23.52/3.51      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.52/3.51      inference(global_propositional_subsumption,
% 23.52/3.51                [status(thm)],
% 23.52/3.51                [c_1400,c_20]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_12,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 23.52/3.51      inference(cnf_transformation,[],[f54]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_218,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | k7_subset_1(X1_44,X0_44,X2_44) = k4_xboole_0(X0_44,X2_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_12]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_564,plain,
% 23.52/3.51      ( k7_subset_1(X0_44,X1_44,X2_44) = k4_xboole_0(X1_44,X2_44)
% 23.52/3.51      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1700,plain,
% 23.52/3.51      ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0_44) = k4_xboole_0(k3_tarski(sK1),X0_44) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_1694,c_564]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_18,negated_conjecture,
% 23.52/3.51      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 23.52/3.51      inference(cnf_transformation,[],[f60]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_212,negated_conjecture,
% 23.52/3.51      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_18]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_570,plain,
% 23.52/3.51      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_933,plain,
% 23.52/3.51      ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_570,c_568]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_17,negated_conjecture,
% 23.52/3.51      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 23.52/3.51      inference(cnf_transformation,[],[f61]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_213,negated_conjecture,
% 23.52/3.51      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_17]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_569,plain,
% 23.52/3.51      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_998,plain,
% 23.52/3.51      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_933,c_569]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_999,plain,
% 23.52/3.51      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(light_normalisation,[status(thm)],[c_998,c_934]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_991,plain,
% 23.52/3.51      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_44) = k4_xboole_0(sK1,X0_44) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_564]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1000,plain,
% 23.52/3.51      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_999,c_991]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2873,plain,
% 23.52/3.51      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_1700,c_1000]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_9,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f51]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_221,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | m1_subset_1(k7_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_9]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_561,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(k7_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1336,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(sK1,X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 23.52/3.51      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_991,c_561]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_3319,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(sK1,X0_44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(global_propositional_subsumption,
% 23.52/3.51                [status(thm)],
% 23.52/3.51                [c_1336,c_20]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_3326,plain,
% 23.52/3.51      ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0_44)) = k3_tarski(k4_xboole_0(sK1,X0_44)) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_3319,c_568]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_71603,plain,
% 23.52/3.51      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_2873,c_3326]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_71605,plain,
% 23.52/3.51      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_868,c_71603]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_0,plain,
% 23.52/3.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 23.52/3.51      inference(cnf_transformation,[],[f42]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_230,plain,
% 23.52/3.51      ( k2_xboole_0(X0_44,k4_xboole_0(X1_44,X0_44)) = k2_xboole_0(X0_44,X1_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_0]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_71606,plain,
% 23.52/3.51      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) != iProver_top ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_71605,c_230]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_11,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.52/3.51      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 23.52/3.51      inference(cnf_transformation,[],[f53]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_219,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | k4_subset_1(X1_44,X2_44,X0_44) = k2_xboole_0(X2_44,X0_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_11]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_563,plain,
% 23.52/3.51      ( k4_subset_1(X0_44,X1_44,X2_44) = k2_xboole_0(X1_44,X2_44)
% 23.52/3.51      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1943,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,sK1) = k2_xboole_0(X0_44,sK1)
% 23.52/3.51      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_563]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2392,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_570,c_1943]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1942,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,sK2) = k2_xboole_0(X0_44,sK2)
% 23.52/3.51      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_570,c_563]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2137,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_1942]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_5,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.52/3.51      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 23.52/3.51      inference(cnf_transformation,[],[f47]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_225,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | k4_subset_1(X1_44,X0_44,X2_44) = k4_subset_1(X1_44,X2_44,X0_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_5]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_557,plain,
% 23.52/3.51      ( k4_subset_1(X0_44,X1_44,X2_44) = k4_subset_1(X0_44,X2_44,X1_44)
% 23.52/3.51      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1213,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,X0_44) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,sK2)
% 23.52/3.51      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_570,c_557]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1497,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_1213]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2221,plain,
% 23.52/3.51      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_2137,c_1497]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2398,plain,
% 23.52/3.51      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 23.52/3.51      inference(light_normalisation,[status(thm)],[c_2392,c_2221]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_71607,plain,
% 23.52/3.51      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) != iProver_top ),
% 23.52/3.51      inference(light_normalisation,[status(thm)],[c_71606,c_2398]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_71610,plain,
% 23.52/3.51      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_556,c_71607]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_6,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.52/3.51      inference(cnf_transformation,[],[f48]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_224,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | k3_subset_1(X1_44,X0_44) = k4_xboole_0(X1_44,X0_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_6]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_558,plain,
% 23.52/3.51      ( k3_subset_1(X0_44,X1_44) = k4_xboole_0(X0_44,X1_44)
% 23.52/3.51      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_799,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_570,c_558]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_7,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f49]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_223,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_7]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_559,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1064,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 23.52/3.51      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_799,c_559]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_21,plain,
% 23.52/3.51      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_4263,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(global_propositional_subsumption,
% 23.52/3.51                [status(thm)],
% 23.52/3.51                [c_1064,c_21]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_13,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 23.52/3.51      inference(cnf_transformation,[],[f55]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_217,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | k9_subset_1(X1_44,X2_44,X0_44) = k3_xboole_0(X2_44,X0_44) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_13]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_565,plain,
% 23.52/3.51      ( k9_subset_1(X0_44,X1_44,X2_44) = k3_xboole_0(X1_44,X2_44)
% 23.52/3.51      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_4270,plain,
% 23.52/3.51      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_44,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_xboole_0(X0_44,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_4263,c_565]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_10,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.52/3.51      inference(cnf_transformation,[],[f52]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_220,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | k3_subset_1(X1_44,k3_subset_1(X1_44,X0_44)) = X0_44 ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_10]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_562,plain,
% 23.52/3.51      ( k3_subset_1(X0_44,k3_subset_1(X0_44,X1_44)) = X1_44
% 23.52/3.51      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_878,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_562]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_800,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_571,c_558]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_879,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
% 23.52/3.51      inference(light_normalisation,[status(thm)],[c_878,c_800]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_14,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.52/3.51      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
% 23.52/3.51      inference(cnf_transformation,[],[f56]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_216,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | r1_tarski(k3_subset_1(X1_44,X2_44),k3_subset_1(X1_44,k9_subset_1(X1_44,X2_44,X0_44))) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_14]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_566,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(X2_44,k1_zfmisc_1(X1_44)) != iProver_top
% 23.52/3.51      | r1_tarski(k3_subset_1(X1_44,X2_44),k3_subset_1(X1_44,k9_subset_1(X1_44,X2_44,X0_44))) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1977,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 23.52/3.51      | m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 23.52/3.51      | r1_tarski(sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),X0_44))) = iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_879,c_566]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_1152,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 23.52/3.51      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_800,c_559]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_53473,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 23.52/3.51      | r1_tarski(sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),X0_44))) = iProver_top ),
% 23.52/3.51      inference(global_propositional_subsumption,
% 23.52/3.51                [status(thm)],
% 23.52/3.51                [c_1977,c_20,c_1152]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_53485,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 23.52/3.51      | r1_tarski(sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))) = iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_4270,c_53473]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2,plain,
% 23.52/3.51      ( k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f44]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_228,plain,
% 23.52/3.51      ( k3_xboole_0(k4_xboole_0(X0_44,X1_44),k4_xboole_0(X0_44,X2_44)) = k4_xboole_0(X0_44,k2_xboole_0(X1_44,X2_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_2]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_8,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.52/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.52/3.51      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 23.52/3.51      inference(cnf_transformation,[],[f50]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_222,plain,
% 23.52/3.51      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 23.52/3.51      | m1_subset_1(k4_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 23.52/3.51      inference(subtyping,[status(esa)],[c_8]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_560,plain,
% 23.52/3.51      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(X2_44,k1_zfmisc_1(X1_44)) != iProver_top
% 23.52/3.51      | m1_subset_1(k4_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 23.52/3.51      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_2222,plain,
% 23.52/3.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 23.52/3.51      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 23.52/3.51      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_2137,c_560]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_5486,plain,
% 23.52/3.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 23.52/3.51      inference(global_propositional_subsumption,
% 23.52/3.51                [status(thm)],
% 23.52/3.51                [c_2222,c_20,c_21]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_5499,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_5486,c_562]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_5500,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) ),
% 23.52/3.51      inference(superposition,[status(thm)],[c_5486,c_558]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_5512,plain,
% 23.52/3.51      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_5499,c_5500]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(c_53493,plain,
% 23.52/3.51      ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 23.52/3.51      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 23.52/3.51      inference(demodulation,[status(thm)],[c_53485,c_228,c_5512]) ).
% 23.52/3.51  
% 23.52/3.51  cnf(contradiction,plain,
% 23.52/3.51      ( $false ),
% 23.52/3.51      inference(minisat,[status(thm)],[c_71610,c_53493,c_1064,c_21]) ).
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.52/3.51  
% 23.52/3.51  ------                               Statistics
% 23.52/3.51  
% 23.52/3.51  ------ General
% 23.52/3.51  
% 23.52/3.51  abstr_ref_over_cycles:                  0
% 23.52/3.51  abstr_ref_under_cycles:                 0
% 23.52/3.51  gc_basic_clause_elim:                   0
% 23.52/3.51  forced_gc_time:                         0
% 23.52/3.51  parsing_time:                           0.009
% 23.52/3.51  unif_index_cands_time:                  0.
% 23.52/3.51  unif_index_add_time:                    0.
% 23.52/3.51  orderings_time:                         0.
% 23.52/3.51  out_proof_time:                         0.019
% 23.52/3.51  total_time:                             2.764
% 23.52/3.51  num_of_symbols:                         49
% 23.52/3.51  num_of_terms:                           101684
% 23.52/3.51  
% 23.52/3.51  ------ Preprocessing
% 23.52/3.51  
% 23.52/3.51  num_of_splits:                          0
% 23.52/3.51  num_of_split_atoms:                     0
% 23.52/3.51  num_of_reused_defs:                     0
% 23.52/3.51  num_eq_ax_congr_red:                    17
% 23.52/3.51  num_of_sem_filtered_clauses:            1
% 23.52/3.51  num_of_subtypes:                        2
% 23.52/3.51  monotx_restored_types:                  0
% 23.52/3.51  sat_num_of_epr_types:                   0
% 23.52/3.51  sat_num_of_non_cyclic_types:            0
% 23.52/3.51  sat_guarded_non_collapsed_types:        1
% 23.52/3.51  num_pure_diseq_elim:                    0
% 23.52/3.51  simp_replaced_by:                       0
% 23.52/3.51  res_preprocessed:                       85
% 23.52/3.51  prep_upred:                             0
% 23.52/3.51  prep_unflattend:                        0
% 23.52/3.51  smt_new_axioms:                         0
% 23.52/3.51  pred_elim_cands:                        2
% 23.52/3.51  pred_elim:                              0
% 23.52/3.51  pred_elim_cl:                           0
% 23.52/3.51  pred_elim_cycles:                       1
% 23.52/3.51  merged_defs:                            0
% 23.52/3.51  merged_defs_ncl:                        0
% 23.52/3.51  bin_hyper_res:                          0
% 23.52/3.51  prep_cycles:                            3
% 23.52/3.51  pred_elim_time:                         0.
% 23.52/3.51  splitting_time:                         0.
% 23.52/3.51  sem_filter_time:                        0.
% 23.52/3.51  monotx_time:                            0.
% 23.52/3.51  subtype_inf_time:                       0.
% 23.52/3.51  
% 23.52/3.51  ------ Problem properties
% 23.52/3.51  
% 23.52/3.51  clauses:                                20
% 23.52/3.51  conjectures:                            3
% 23.52/3.51  epr:                                    0
% 23.52/3.51  horn:                                   20
% 23.52/3.51  ground:                                 3
% 23.52/3.51  unary:                                  6
% 23.52/3.51  binary:                                 10
% 23.52/3.51  lits:                                   38
% 23.52/3.51  lits_eq:                                10
% 23.52/3.51  fd_pure:                                0
% 23.52/3.51  fd_pseudo:                              0
% 23.52/3.51  fd_cond:                                0
% 23.52/3.51  fd_pseudo_cond:                         0
% 23.52/3.51  ac_symbols:                             0
% 23.52/3.51  
% 23.52/3.51  ------ Propositional Solver
% 23.52/3.51  
% 23.52/3.51  prop_solver_calls:                      36
% 23.52/3.51  prop_fast_solver_calls:                 1372
% 23.52/3.51  smt_solver_calls:                       0
% 23.52/3.51  smt_fast_solver_calls:                  0
% 23.52/3.51  prop_num_of_clauses:                    30781
% 23.52/3.51  prop_preprocess_simplified:             37390
% 23.52/3.51  prop_fo_subsumed:                       56
% 23.52/3.51  prop_solver_time:                       0.
% 23.52/3.51  smt_solver_time:                        0.
% 23.52/3.51  smt_fast_solver_time:                   0.
% 23.52/3.51  prop_fast_solver_time:                  0.
% 23.52/3.51  prop_unsat_core_time:                   0.004
% 23.52/3.51  
% 23.52/3.51  ------ QBF
% 23.52/3.51  
% 23.52/3.51  qbf_q_res:                              0
% 23.52/3.51  qbf_num_tautologies:                    0
% 23.52/3.51  qbf_prep_cycles:                        0
% 23.52/3.51  
% 23.52/3.51  ------ BMC1
% 23.52/3.51  
% 23.52/3.51  bmc1_current_bound:                     -1
% 23.52/3.51  bmc1_last_solved_bound:                 -1
% 23.52/3.51  bmc1_unsat_core_size:                   -1
% 23.52/3.51  bmc1_unsat_core_parents_size:           -1
% 23.52/3.51  bmc1_merge_next_fun:                    0
% 23.52/3.51  bmc1_unsat_core_clauses_time:           0.
% 23.52/3.51  
% 23.52/3.51  ------ Instantiation
% 23.52/3.51  
% 23.52/3.51  inst_num_of_clauses:                    7377
% 23.52/3.51  inst_num_in_passive:                    2605
% 23.52/3.51  inst_num_in_active:                     2711
% 23.52/3.51  inst_num_in_unprocessed:                2064
% 23.52/3.51  inst_num_of_loops:                      2900
% 23.52/3.51  inst_num_of_learning_restarts:          0
% 23.52/3.51  inst_num_moves_active_passive:          180
% 23.52/3.51  inst_lit_activity:                      0
% 23.52/3.51  inst_lit_activity_moves:                3
% 23.52/3.51  inst_num_tautologies:                   0
% 23.52/3.51  inst_num_prop_implied:                  0
% 23.52/3.51  inst_num_existing_simplified:           0
% 23.52/3.51  inst_num_eq_res_simplified:             0
% 23.52/3.51  inst_num_child_elim:                    0
% 23.52/3.51  inst_num_of_dismatching_blockings:      11375
% 23.52/3.51  inst_num_of_non_proper_insts:           11953
% 23.52/3.51  inst_num_of_duplicates:                 0
% 23.52/3.51  inst_inst_num_from_inst_to_res:         0
% 23.52/3.51  inst_dismatching_checking_time:         0.
% 23.52/3.51  
% 23.52/3.51  ------ Resolution
% 23.52/3.51  
% 23.52/3.51  res_num_of_clauses:                     0
% 23.52/3.51  res_num_in_passive:                     0
% 23.52/3.51  res_num_in_active:                      0
% 23.52/3.51  res_num_of_loops:                       88
% 23.52/3.51  res_forward_subset_subsumed:            545
% 23.52/3.51  res_backward_subset_subsumed:           16
% 23.52/3.51  res_forward_subsumed:                   0
% 23.52/3.51  res_backward_subsumed:                  0
% 23.52/3.51  res_forward_subsumption_resolution:     0
% 23.52/3.51  res_backward_subsumption_resolution:    0
% 23.52/3.51  res_clause_to_clause_subsumption:       12559
% 23.52/3.51  res_orphan_elimination:                 0
% 23.52/3.51  res_tautology_del:                      1305
% 23.52/3.51  res_num_eq_res_simplified:              0
% 23.52/3.51  res_num_sel_changes:                    0
% 23.52/3.51  res_moves_from_active_to_pass:          0
% 23.52/3.51  
% 23.52/3.51  ------ Superposition
% 23.52/3.51  
% 23.52/3.51  sup_time_total:                         0.
% 23.52/3.51  sup_time_generating:                    0.
% 23.52/3.51  sup_time_sim_full:                      0.
% 23.52/3.51  sup_time_sim_immed:                     0.
% 23.52/3.51  
% 23.52/3.51  sup_num_of_clauses:                     4684
% 23.52/3.51  sup_num_in_active:                      541
% 23.52/3.51  sup_num_in_passive:                     4143
% 23.52/3.51  sup_num_of_loops:                       579
% 23.52/3.51  sup_fw_superposition:                   3342
% 23.52/3.51  sup_bw_superposition:                   2079
% 23.52/3.51  sup_immediate_simplified:               3877
% 23.52/3.51  sup_given_eliminated:                   0
% 23.52/3.51  comparisons_done:                       0
% 23.52/3.51  comparisons_avoided:                    0
% 23.52/3.51  
% 23.52/3.51  ------ Simplifications
% 23.52/3.51  
% 23.52/3.51  
% 23.52/3.51  sim_fw_subset_subsumed:                 7
% 23.52/3.51  sim_bw_subset_subsumed:                 1
% 23.52/3.51  sim_fw_subsumed:                        8
% 23.52/3.51  sim_bw_subsumed:                        0
% 23.52/3.51  sim_fw_subsumption_res:                 0
% 23.52/3.51  sim_bw_subsumption_res:                 0
% 23.52/3.51  sim_tautology_del:                      0
% 23.52/3.51  sim_eq_tautology_del:                   585
% 23.52/3.51  sim_eq_res_simp:                        0
% 23.52/3.51  sim_fw_demodulated:                     1456
% 23.52/3.51  sim_bw_demodulated:                     907
% 23.52/3.51  sim_light_normalised:                   1803
% 23.52/3.51  sim_joinable_taut:                      0
% 23.52/3.51  sim_joinable_simp:                      0
% 23.52/3.51  sim_ac_normalised:                      0
% 23.52/3.51  sim_smt_subsumption:                    0
% 23.52/3.51  
%------------------------------------------------------------------------------
