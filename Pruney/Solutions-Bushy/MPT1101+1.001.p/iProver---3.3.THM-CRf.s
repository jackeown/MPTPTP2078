%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1101+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:53 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 139 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),sK1,k3_subset_1(u1_struct_0(X0),sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X1,k3_subset_1(u1_struct_0(sK0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10,f9])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_61,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_62,plain,
    ( k4_subset_1(X0,sK1,k3_subset_1(X0,sK1)) = k2_subset_1(X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_5,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_55,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_56,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_55])).

cnf(c_99,plain,
    ( k4_subset_1(X0,sK1,k3_subset_1(X0,sK1)) = X0
    | k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_62,c_1,c_56])).

cnf(c_133,plain,
    ( k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_99])).

cnf(c_3,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_96,plain,
    ( k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3,c_56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_133,c_96])).


%------------------------------------------------------------------------------
