%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0986+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:35 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 116 expanded)
%              Number of clauses        :   36 (  38 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   18
%              Number of atoms          :  224 ( 620 expanded)
%              Number of equality atoms :  113 ( 225 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & v2_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f16])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_173,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X1)) = X1
    | k1_relat_1(X0) != sK0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_174,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) = sK2
    | k1_relat_1(X0) != sK0 ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_244,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) = sK2
    | k1_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_174])).

cnf(c_245,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) = sK2
    | k1_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,negated_conjecture,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_247,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_245,c_16,c_10])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_247])).

cnf(c_262,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_386,plain,
    ( k1_relat_1(sK3) != sK0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_262])).

cnf(c_491,plain,
    ( k1_relat_1(sK3) != sK0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_386])).

cnf(c_501,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_276,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_277,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_505,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_578,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_505])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_285,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_286,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_438,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != X0
    | sK1 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_286])).

cnf(c_439,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_440,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_11])).

cnf(c_441,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_490,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_441])).

cnf(c_502,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_490])).

cnf(c_645,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_578,c_502])).

cnf(c_649,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_645])).

cnf(c_653,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_649])).


%------------------------------------------------------------------------------
