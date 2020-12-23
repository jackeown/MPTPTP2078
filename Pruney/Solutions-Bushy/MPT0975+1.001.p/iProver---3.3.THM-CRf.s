%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0975+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:33 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 140 expanded)
%              Number of clauses        :   43 (  45 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  264 ( 862 expanded)
%              Number of equality atoms :  122 ( 284 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_relat_1(X4) )
           => ( r2_hidden(X2,X0)
             => ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
                | k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) != k1_funct_1(k5_relat_1(X3,X4),X2)
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) != k1_funct_1(k5_relat_1(X3,X4),X2)
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) != k1_funct_1(k5_relat_1(X3,X4),X2)
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( k1_funct_1(k5_relat_1(X3,sK4),X2) != k1_funct_1(sK4,k1_funct_1(X3,X2))
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & v1_funct_1(sK4)
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k1_funct_1(X4,k1_funct_1(X3,X2)) != k1_funct_1(k5_relat_1(X3,X4),X2)
            & k1_xboole_0 != X1
            & r2_hidden(X2,X0)
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k1_funct_1(X4,k1_funct_1(sK3,sK2)) != k1_funct_1(k5_relat_1(sK3,X4),sK2)
          & k1_xboole_0 != sK1
          & r2_hidden(sK2,sK0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f17,f16])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_201,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_202,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_463,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_45,X1_45,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_723,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_463])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_210,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_211,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_364,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != X0
    | sK1 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_211])).

cnf(c_365,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_366,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_10])).

cnf(c_367,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_421,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_367])).

cnf(c_459,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_793,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_723,c_459])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_170,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_funct_1(k5_relat_1(X1,X0),X2)
    | k1_relat_1(X1) != sK0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_171,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X0,k1_funct_1(X1,sK2)) = k1_funct_1(k5_relat_1(X1,X0),sK2)
    | k1_relat_1(X1) != sK0 ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_464,plain,
    ( ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45)
    | k1_funct_1(X0_45,k1_funct_1(X1_45,sK2)) = k1_funct_1(k5_relat_1(X1_45,X0_45),sK2)
    | k1_relat_1(X1_45) != sK0 ),
    inference(subtyping,[status(esa)],[c_171])).

cnf(c_665,plain,
    ( ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,k1_funct_1(X0_45,sK2)) = k1_funct_1(k5_relat_1(X0_45,sK4),sK2)
    | k1_relat_1(X0_45) != sK0 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_739,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2)) = k1_funct_1(k5_relat_1(sK3,sK4),sK2)
    | k1_relat_1(sK3) != sK0 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_474,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_730,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(k5_relat_1(sK3,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_477,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_709,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != X0_48
    | k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2)) != X0_48 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_729,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(k5_relat_1(sK3,sK4),sK2)
    | k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2)) != k1_funct_1(k5_relat_1(sK3,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_246,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_247,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_462,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_679,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_472,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_677,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_9,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_469,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_793,c_739,c_730,c_729,c_679,c_677,c_469,c_12,c_13,c_16])).


%------------------------------------------------------------------------------
