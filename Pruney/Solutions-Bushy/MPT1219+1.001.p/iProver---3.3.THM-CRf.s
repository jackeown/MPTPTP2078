%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1219+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:11 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   38 (  66 expanded)
%              Number of clauses        :   23 (  24 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 216 expanded)
%              Number of equality atoms :   59 ( 123 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
             => X1 = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f6])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2 != X1
        & k3_subset_1(u1_struct_0(X0),sK2) = k3_subset_1(u1_struct_0(X0),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( sK1 != sK2
    & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9,f8])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_48,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_49,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK1)) = sK1
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_66,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_36)
    | k3_subset_1(X0_36,k3_subset_1(X0_36,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_125,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution,[status(thm)],[c_66])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_39,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_40,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_39])).

cnf(c_67,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_36)
    | k3_subset_1(X0_36,k3_subset_1(X0_36,sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_128,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_67])).

cnf(c_2,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_68,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_129,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_128,c_68])).

cnf(c_166,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_125,c_129])).

cnf(c_72,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_95,plain,
    ( sK2 != X0_35
    | sK1 != X0_35
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_96,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_1,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_69,negated_conjecture,
    ( sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_70,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_76,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_166,c_96,c_69,c_76])).


%------------------------------------------------------------------------------
