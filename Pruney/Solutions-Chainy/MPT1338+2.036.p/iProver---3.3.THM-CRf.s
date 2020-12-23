%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:06 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  236 (1650 expanded)
%              Number of clauses        :  135 ( 467 expanded)
%              Number of leaves         :   31 ( 493 expanded)
%              Depth                    :   24
%              Number of atoms          :  728 (11554 expanded)
%              Number of equality atoms :  305 (3976 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK6)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK6)) != k2_struct_0(X1) )
        & v2_funct_1(sK6)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK6) = k2_struct_0(X1)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK5),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK5),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK5),X2)) != k2_struct_0(sK5) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),X2) = k2_struct_0(sK5)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5))
            & v1_funct_1(X2) )
        & l1_struct_0(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                  | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(X1),X2)) != k2_struct_0(sK4)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
      | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) )
    & v2_funct_1(sK6)
    & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5)
    & l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f50,f65,f64,f63])).

fof(f111,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f99,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,(
    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f110,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f109,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f86,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f85,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f59])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f107,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f73])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f73])).

fof(f122,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f118])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f55])).

fof(f77,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f120,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f115,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f78,f73])).

fof(f116,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f74,f115])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f22,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f61])).

fof(f102,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2929,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_30,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_43,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_591,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_43])).

cnf(c_592,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_45,negated_conjecture,
    ( l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_596,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_45])).

cnf(c_597,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_2988,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2929,c_592,c_597])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2938,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5323,plain,
    ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2988,c_2938])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2981,plain,
    ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
    inference(light_normalisation,[status(thm)],[c_39,c_592,c_597])).

cnf(c_5429,plain,
    ( k2_struct_0(sK5) = k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_5323,c_2981])).

cnf(c_5441,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_relat_1(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5429,c_2988])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2939,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6477,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_5441,c_2939])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2932,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3886,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
    | k2_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2988,c_2932])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2928,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2975,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2928,c_592,c_597])).

cnf(c_4281,plain,
    ( k2_struct_0(sK5) = k1_xboole_0
    | k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_2975])).

cnf(c_4282,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
    | k2_struct_0(sK5) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4281])).

cnf(c_5436,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k2_struct_0(sK4)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5429,c_4282])).

cnf(c_7206,plain,
    ( k2_struct_0(sK4) = k1_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6477,c_5436])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_38,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_907,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_908,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_912,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK6,X0,X1)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_42])).

cnf(c_913,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(renaming,[status(thm)],[c_912])).

cnf(c_2922,plain,
    ( k2_relset_1(X0,X1,sK6) != X1
    | v1_funct_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_3833,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_2922])).

cnf(c_3836,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3833,c_2975,c_2988])).

cnf(c_5437,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),k2_struct_0(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5429,c_3836])).

cnf(c_6627,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(k2_funct_1(sK6)) ),
    inference(superposition,[status(thm)],[c_5437,c_2938])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_945,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_946,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_945])).

cnf(c_948,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_42])).

cnf(c_985,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_948])).

cnf(c_986,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_2921,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_3220,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_3878,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2921,c_40,c_3220])).

cnf(c_6630,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_6627,c_3878])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_835,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_38])).

cnf(c_836,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_840,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK6,X0,X1)
    | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_42])).

cnf(c_841,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(renaming,[status(thm)],[c_840])).

cnf(c_2924,plain,
    ( k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1
    | v1_funct_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_3600,plain,
    ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6)
    | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_2924])).

cnf(c_3659,plain,
    ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3600,c_2975,c_2988])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3107,plain,
    ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK4)
    | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
    inference(light_normalisation,[status(thm)],[c_37,c_592,c_597])).

cnf(c_3662,plain,
    ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
    | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK5) ),
    inference(demodulation,[status(thm)],[c_3659,c_3107])).

cnf(c_5438,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
    | k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_5429,c_3662])).

cnf(c_6626,plain,
    ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
    inference(superposition,[status(thm)],[c_5437,c_2939])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_931,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_932,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_934,plain,
    ( ~ v1_relat_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_42])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_934])).

cnf(c_998,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_997])).

cnf(c_2920,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_3223,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_3338,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2920,c_40,c_3223])).

cnf(c_6633,plain,
    ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_6626,c_3338])).

cnf(c_6654,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5438,c_6633])).

cnf(c_7210,plain,
    ( k2_struct_0(sK4) != k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_6630,c_6654])).

cnf(c_8001,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7206,c_7210])).

cnf(c_32,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_565,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_44])).

cnf(c_566,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_43])).

cnf(c_2926,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_2972,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2926,c_592])).

cnf(c_5443,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_relat_1(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5429,c_2972])).

cnf(c_8018,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8001,c_5443])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2942,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9250,plain,
    ( r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8018,c_2942])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_115,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_124,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_127,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_130,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_136,plain,
    ( v1_xboole_0(sK1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_147,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_660,plain,
    ( sK1(X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_661,plain,
    ( k1_xboole_0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_662,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_273,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_12])).

cnf(c_2927,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_6,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2967,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2927,c_6])).

cnf(c_3157,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2967])).

cnf(c_3159,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_2126,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3250,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X1))
    | X0 != sK1(X1) ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_3252,plain,
    ( ~ v1_xboole_0(sK1(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3250])).

cnf(c_2129,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3342,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_3344,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3342])).

cnf(c_4199,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0))
    | k1_xboole_0 = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4202,plain,
    ( k1_xboole_0 = k1_zfmisc_1(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4199])).

cnf(c_4204,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4202])).

cnf(c_12012,plain,
    ( r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9250,c_115,c_124,c_127,c_130,c_136,c_147,c_662,c_3159,c_3252,c_3344,c_4204])).

cnf(c_5,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2930,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5066,plain,
    ( k1_xboole_0 != X0
    | k1_xboole_0 = X1
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2930])).

cnf(c_5072,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5066])).

cnf(c_12020,plain,
    ( sK2(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12012,c_5072])).

cnf(c_4146,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK5))
    | sK2(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_4148,plain,
    ( v1_xboole_0(sK2(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4146])).

cnf(c_31,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_576,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_44])).

cnf(c_577,plain,
    ( ~ l1_struct_0(sK5)
    | ~ v1_xboole_0(sK2(sK5)) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12020,c_4148,c_3252,c_662,c_577,c_136,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.52/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/1.00  
% 3.52/1.00  ------  iProver source info
% 3.52/1.00  
% 3.52/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.52/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/1.00  git: non_committed_changes: false
% 3.52/1.00  git: last_make_outside_of_git: false
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    --mode clausify
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     num_symb
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       true
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  ------ Parsing...
% 3.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.00  ------ Proving...
% 3.52/1.00  ------ Problem Properties 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  clauses                                 40
% 3.52/1.00  conjectures                             4
% 3.52/1.00  EPR                                     2
% 3.52/1.00  Horn                                    33
% 3.52/1.00  unary                                   14
% 3.52/1.00  binary                                  10
% 3.52/1.00  lits                                    88
% 3.52/1.00  lits eq                                 33
% 3.52/1.00  fd_pure                                 0
% 3.52/1.00  fd_pseudo                               0
% 3.52/1.00  fd_cond                                 6
% 3.52/1.00  fd_pseudo_cond                          2
% 3.52/1.00  AC symbols                              0
% 3.52/1.00  
% 3.52/1.00  ------ Schedule dynamic 5 is on 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  Current options:
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    --mode clausify
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     none
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       false
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ Proving...
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS status Theorem for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  fof(f24,conjecture,(
% 3.52/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f25,negated_conjecture,(
% 3.52/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.52/1.00    inference(negated_conjecture,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f49,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.52/1.00    inference(ennf_transformation,[],[f25])).
% 3.52/1.00  
% 3.52/1.00  fof(f50,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.52/1.00    inference(flattening,[],[f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f65,plain,(
% 3.52/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK6)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK6)) != k2_struct_0(X1)) & v2_funct_1(sK6) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK6) = k2_struct_0(X1) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f64,plain,(
% 3.52/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK5),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK5),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK5),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK5),X2)) != k2_struct_0(sK5)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),X2) = k2_struct_0(sK5) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))) )),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f63,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(X1),X2)) != k2_struct_0(sK4) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK4))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f66,plain,(
% 3.52/1.00    (((k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4) | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5)) & v2_funct_1(sK6) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)) & l1_struct_0(sK4)),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f50,f65,f64,f63])).
% 3.52/1.00  
% 3.52/1.00  fof(f111,plain,(
% 3.52/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f20,axiom,(
% 3.52/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f43,plain,(
% 3.52/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.52/1.00    inference(ennf_transformation,[],[f20])).
% 3.52/1.00  
% 3.52/1.00  fof(f99,plain,(
% 3.52/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f43])).
% 3.52/1.00  
% 3.52/1.00  fof(f108,plain,(
% 3.52/1.00    l1_struct_0(sK5)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f106,plain,(
% 3.52/1.00    l1_struct_0(sK4)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f17,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f38,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f17])).
% 3.52/1.00  
% 3.52/1.00  fof(f89,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f38])).
% 3.52/1.00  
% 3.52/1.00  fof(f112,plain,(
% 3.52/1.00    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f16,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f37,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f16])).
% 3.52/1.00  
% 3.52/1.00  fof(f88,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f37])).
% 3.52/1.00  
% 3.52/1.00  fof(f18,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f39,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f18])).
% 3.52/1.00  
% 3.52/1.00  fof(f40,plain,(
% 3.52/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(flattening,[],[f39])).
% 3.52/1.00  
% 3.52/1.00  fof(f58,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(nnf_transformation,[],[f40])).
% 3.52/1.00  
% 3.52/1.00  fof(f90,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f58])).
% 3.52/1.00  
% 3.52/1.00  fof(f110,plain,(
% 3.52/1.00    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f19,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f41,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f19])).
% 3.52/1.00  
% 3.52/1.00  fof(f42,plain,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f41])).
% 3.52/1.00  
% 3.52/1.00  fof(f98,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f42])).
% 3.52/1.00  
% 3.52/1.00  fof(f113,plain,(
% 3.52/1.00    v2_funct_1(sK6)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f109,plain,(
% 3.52/1.00    v1_funct_1(sK6)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f15,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f36,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.00    inference(ennf_transformation,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f87,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f36])).
% 3.52/1.00  
% 3.52/1.00  fof(f14,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f34,plain,(
% 3.52/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f14])).
% 3.52/1.00  
% 3.52/1.00  fof(f35,plain,(
% 3.52/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f34])).
% 3.52/1.00  
% 3.52/1.00  fof(f86,plain,(
% 3.52/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f35])).
% 3.52/1.00  
% 3.52/1.00  fof(f23,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f47,plain,(
% 3.52/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  fof(f48,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f47])).
% 3.52/1.00  
% 3.52/1.00  fof(f105,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f48])).
% 3.52/1.00  
% 3.52/1.00  fof(f114,plain,(
% 3.52/1.00    k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4) | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f85,plain,(
% 3.52/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f35])).
% 3.52/1.00  
% 3.52/1.00  fof(f21,axiom,(
% 3.52/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f44,plain,(
% 3.52/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  fof(f45,plain,(
% 3.52/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.52/1.00    inference(flattening,[],[f44])).
% 3.52/1.00  
% 3.52/1.00  fof(f59,plain,(
% 3.52/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f60,plain,(
% 3.52/1.00    ! [X0] : ((~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f59])).
% 3.52/1.00  
% 3.52/1.00  fof(f100,plain,(
% 3.52/1.00    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f60])).
% 3.52/1.00  
% 3.52/1.00  fof(f107,plain,(
% 3.52/1.00    ~v2_struct_0(sK5)),
% 3.52/1.00    inference(cnf_transformation,[],[f66])).
% 3.52/1.00  
% 3.52/1.00  fof(f11,axiom,(
% 3.52/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f29,plain,(
% 3.52/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.52/1.00    inference(ennf_transformation,[],[f11])).
% 3.52/1.00  
% 3.52/1.00  fof(f30,plain,(
% 3.52/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.52/1.00    inference(flattening,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f82,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f30])).
% 3.52/1.00  
% 3.52/1.00  fof(f13,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f33,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.52/1.00    inference(ennf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f84,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f33])).
% 3.52/1.00  
% 3.52/1.00  fof(f10,axiom,(
% 3.52/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f81,plain,(
% 3.52/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f10])).
% 3.52/1.00  
% 3.52/1.00  fof(f9,axiom,(
% 3.52/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f28,plain,(
% 3.52/1.00    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f9])).
% 3.52/1.00  
% 3.52/1.00  fof(f57,plain,(
% 3.52/1.00    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/1.00    inference(nnf_transformation,[],[f28])).
% 3.52/1.00  
% 3.52/1.00  fof(f79,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f57])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f73,plain,(
% 3.52/1.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f119,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f79,f73])).
% 3.52/1.00  
% 3.52/1.00  fof(f80,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f57])).
% 3.52/1.00  
% 3.52/1.00  fof(f118,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f80,f73])).
% 3.52/1.00  
% 3.52/1.00  fof(f122,plain,(
% 3.52/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.52/1.00    inference(equality_resolution,[],[f118])).
% 3.52/1.00  
% 3.52/1.00  fof(f7,axiom,(
% 3.52/1.00    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f55,plain,(
% 3.52/1.00    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f56,plain,(
% 3.52/1.00    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f55])).
% 3.52/1.00  
% 3.52/1.00  fof(f77,plain,(
% 3.52/1.00    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f56])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f51,plain,(
% 3.52/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.52/1.00    inference(nnf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f52,plain,(
% 3.52/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.52/1.00    inference(rectify,[],[f51])).
% 3.52/1.00  
% 3.52/1.00  fof(f53,plain,(
% 3.52/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f54,plain,(
% 3.52/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f69,plain,(
% 3.52/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.52/1.00    inference(cnf_transformation,[],[f54])).
% 3.52/1.00  
% 3.52/1.00  fof(f120,plain,(
% 3.52/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.52/1.00    inference(equality_resolution,[],[f69])).
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f27,plain,(
% 3.52/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.52/1.00    inference(ennf_transformation,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f67,plain,(
% 3.52/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f5,axiom,(
% 3.52/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f74,plain,(
% 3.52/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.52/1.00    inference(cnf_transformation,[],[f5])).
% 3.52/1.00  
% 3.52/1.00  fof(f8,axiom,(
% 3.52/1.00    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f78,plain,(
% 3.52/1.00    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f115,plain,(
% 3.52/1.00    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f78,f73])).
% 3.52/1.00  
% 3.52/1.00  fof(f116,plain,(
% 3.52/1.00    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.52/1.00    inference(definition_unfolding,[],[f74,f115])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f72,plain,(
% 3.52/1.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.52/1.00    inference(cnf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f22,axiom,(
% 3.52/1.00    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f26,plain,(
% 3.52/1.00    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 3.52/1.00    inference(rectify,[],[f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f46,plain,(
% 3.52/1.00    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f26])).
% 3.52/1.00  
% 3.52/1.00  fof(f61,plain,(
% 3.52/1.00    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f62,plain,(
% 3.52/1.00    ! [X0] : (((r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f61])).
% 3.52/1.00  
% 3.52/1.00  fof(f102,plain,(
% 3.52/1.00    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 3.52/1.00    inference(cnf_transformation,[],[f62])).
% 3.52/1.00  
% 3.52/1.00  fof(f101,plain,(
% 3.52/1.00    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f60])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_40,negated_conjecture,
% 3.52/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2929,plain,
% 3.52/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_30,plain,
% 3.52/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_43,negated_conjecture,
% 3.52/1.00      ( l1_struct_0(sK5) ),
% 3.52/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_591,plain,
% 3.52/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK5 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_43]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_592,plain,
% 3.52/1.00      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_591]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_45,negated_conjecture,
% 3.52/1.00      ( l1_struct_0(sK4) ),
% 3.52/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_596,plain,
% 3.52/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_45]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_597,plain,
% 3.52/1.00      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_596]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2988,plain,
% 3.52/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_2929,c_592,c_597]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_20,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2938,plain,
% 3.52/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5323,plain,
% 3.52/1.00      ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2988,c_2938]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_39,negated_conjecture,
% 3.52/1.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
% 3.52/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2981,plain,
% 3.52/1.00      ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_39,c_592,c_597]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5429,plain,
% 3.52/1.00      ( k2_struct_0(sK5) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5323,c_2981]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5441,plain,
% 3.52/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_relat_1(sK6)))) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5429,c_2988]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_19,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2939,plain,
% 3.52/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6477,plain,
% 3.52/1.00      ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5441,c_2939]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_26,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.52/1.00      | k1_xboole_0 = X2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2932,plain,
% 3.52/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.52/1.00      | k1_xboole_0 = X1
% 3.52/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3886,plain,
% 3.52/1.00      ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
% 3.52/1.00      | k2_struct_0(sK5) = k1_xboole_0
% 3.52/1.00      | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2988,c_2932]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_41,negated_conjecture,
% 3.52/1.00      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2928,plain,
% 3.52/1.00      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2975,plain,
% 3.52/1.00      ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_2928,c_592,c_597]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4281,plain,
% 3.52/1.00      ( k2_struct_0(sK5) = k1_xboole_0
% 3.52/1.00      | k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_3886,c_2975]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4282,plain,
% 3.52/1.00      ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
% 3.52/1.00      | k2_struct_0(sK5) = k1_xboole_0 ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_4281]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5436,plain,
% 3.52/1.00      ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k2_struct_0(sK4)
% 3.52/1.00      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5429,c_4282]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7206,plain,
% 3.52/1.00      ( k2_struct_0(sK4) = k1_relat_1(sK6)
% 3.52/1.00      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_6477,c_5436]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_27,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v2_funct_1(X0)
% 3.52/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_38,negated_conjecture,
% 3.52/1.00      ( v2_funct_1(sK6) ),
% 3.52/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_907,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.52/1.00      | sK6 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_908,plain,
% 3.52/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.52/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | ~ v1_funct_1(sK6)
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_907]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_42,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK6) ),
% 3.52/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_912,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.52/1.00      | ~ v1_funct_2(sK6,X0,X1)
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_908,c_42]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_913,plain,
% 3.52/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.52/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_912]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2922,plain,
% 3.52/1.00      ( k2_relset_1(X0,X1,sK6) != X1
% 3.52/1.00      | v1_funct_2(sK6,X0,X1) != iProver_top
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.52/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3833,plain,
% 3.52/1.00      ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 3.52/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top
% 3.52/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2981,c_2922]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3836,plain,
% 3.52/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_3833,c_2975,c_2988]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5437,plain,
% 3.52/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),k2_struct_0(sK4)))) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5429,c_3836]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6627,plain,
% 3.52/1.00      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(k2_funct_1(sK6)) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5437,c_2938]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_18,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_16,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v2_funct_1(X0)
% 3.52/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_945,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.52/1.00      | sK6 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_38]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_946,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK6)
% 3.52/1.00      | ~ v1_funct_1(sK6)
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_945]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_948,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK6)
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_946,c_42]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_985,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
% 3.52/1.00      | sK6 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_948]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_986,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_985]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2921,plain,
% 3.52/1.00      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
% 3.52/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3220,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 3.52/1.00      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3878,plain,
% 3.52/1.00      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2921,c_40,c_3220]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6630,plain,
% 3.52/1.00      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_6627,c_3878]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_36,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v2_funct_1(X0)
% 3.52/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.52/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_835,plain,
% 3.52/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.52/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.52/1.00      | sK6 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_38]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_836,plain,
% 3.52/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 3.52/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | ~ v1_funct_1(sK6)
% 3.52/1.00      | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_835]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_840,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | ~ v1_funct_2(sK6,X0,X1)
% 3.52/1.00      | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_836,c_42]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_841,plain,
% 3.52/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 3.52/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_840]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2924,plain,
% 3.52/1.00      ( k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.52/1.00      | k2_relset_1(X0,X1,sK6) != X1
% 3.52/1.00      | v1_funct_2(sK6,X0,X1) != iProver_top
% 3.52/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3600,plain,
% 3.52/1.00      ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6)
% 3.52/1.00      | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 3.52/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2981,c_2924]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3659,plain,
% 3.52/1.00      ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_3600,c_2975,c_2988]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_37,negated_conjecture,
% 3.52/1.00      ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
% 3.52/1.00      | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
% 3.52/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3107,plain,
% 3.52/1.00      ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK4)
% 3.52/1.00      | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_37,c_592,c_597]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3662,plain,
% 3.52/1.00      ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
% 3.52/1.00      | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK5) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_3659,c_3107]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5438,plain,
% 3.52/1.00      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
% 3.52/1.00      | k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_relat_1(sK6) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5429,c_3662]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6626,plain,
% 3.52/1.00      ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5437,c_2939]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_17,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v2_funct_1(X0)
% 3.52/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_931,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.52/1.00      | sK6 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_932,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK6)
% 3.52/1.00      | ~ v1_funct_1(sK6)
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_931]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_934,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK6)
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_932,c_42]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_997,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
% 3.52/1.00      | sK6 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_934]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_998,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_997]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2920,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
% 3.52/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3223,plain,
% 3.52/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 3.52/1.00      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_998]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3338,plain,
% 3.52/1.00      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2920,c_40,c_3223]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6633,plain,
% 3.52/1.00      ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_6626,c_3338]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6654,plain,
% 3.52/1.00      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_5438,c_6633]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7210,plain,
% 3.52/1.00      ( k2_struct_0(sK4) != k1_relat_1(sK6) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_6630,c_6654]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8001,plain,
% 3.52/1.00      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_7206,c_7210]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_32,plain,
% 3.52/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.52/1.00      | v2_struct_0(X0)
% 3.52/1.00      | ~ l1_struct_0(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_44,negated_conjecture,
% 3.52/1.00      ( ~ v2_struct_0(sK5) ),
% 3.52/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_565,plain,
% 3.52/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.52/1.00      | ~ l1_struct_0(X0)
% 3.52/1.00      | sK5 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_44]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_566,plain,
% 3.52/1.00      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.52/1.00      | ~ l1_struct_0(sK5) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_568,plain,
% 3.52/1.00      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_566,c_43]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2926,plain,
% 3.52/1.00      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2972,plain,
% 3.52/1.00      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_2926,c_592]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5443,plain,
% 3.52/1.00      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_relat_1(sK6))) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_5429,c_2972]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8018,plain,
% 3.52/1.00      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_8001,c_5443]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_13,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2942,plain,
% 3.52/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.52/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.52/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9250,plain,
% 3.52/1.00      ( r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.52/1.00      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_8018,c_2942]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_15,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/1.00      | ~ r2_hidden(X2,X0)
% 3.52/1.00      | ~ v1_xboole_0(X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_115,plain,
% 3.52/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.52/1.00      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.52/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12,plain,
% 3.52/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_124,plain,
% 3.52/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/1.00      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 3.52/1.00      | k1_xboole_0 = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_127,plain,
% 3.52/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.52/1.00      | ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0))
% 3.52/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10,plain,
% 3.52/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 3.52/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_130,plain,
% 3.52/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.52/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8,plain,
% 3.52/1.00      ( v1_xboole_0(sK1(X0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_136,plain,
% 3.52/1.00      ( v1_xboole_0(sK1(k1_xboole_0)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3,plain,
% 3.52/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_147,plain,
% 3.52/1.00      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.52/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_0,plain,
% 3.52/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_660,plain,
% 3.52/1.00      ( sK1(X0) != X1 | k1_xboole_0 = X1 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_661,plain,
% 3.52/1.00      ( k1_xboole_0 = sK1(X0) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_660]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_662,plain,
% 3.52/1.00      ( k1_xboole_0 = sK1(k1_xboole_0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_661]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_273,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_10,c_12]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2927,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6,plain,
% 3.52/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2967,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_2927,c_6]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3157,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.52/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2967]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3159,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3157]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2126,plain,
% 3.52/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.52/1.00      theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3250,plain,
% 3.52/1.00      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK1(X1)) | X0 != sK1(X1) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2126]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3252,plain,
% 3.52/1.00      ( ~ v1_xboole_0(sK1(k1_xboole_0))
% 3.52/1.00      | v1_xboole_0(k1_xboole_0)
% 3.52/1.00      | k1_xboole_0 != sK1(k1_xboole_0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3250]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2129,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/1.00      theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3342,plain,
% 3.52/1.00      ( r2_hidden(X0,X1)
% 3.52/1.00      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 3.52/1.00      | X0 != X2
% 3.52/1.00      | X1 != k1_zfmisc_1(X3) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2129]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3344,plain,
% 3.52/1.00      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.52/1.00      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.52/1.00      | k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
% 3.52/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3342]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4199,plain,
% 3.52/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) | k1_xboole_0 = k1_zfmisc_1(X0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4202,plain,
% 3.52/1.00      ( k1_xboole_0 = k1_zfmisc_1(X0)
% 3.52/1.00      | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_4199]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4204,plain,
% 3.52/1.00      ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
% 3.52/1.00      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_4202]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12012,plain,
% 3.52/1.00      ( r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_9250,c_115,c_124,c_127,c_130,c_136,c_147,c_662,c_3159,
% 3.52/1.00                 c_3252,c_3344,c_4204]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5,plain,
% 3.52/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_35,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,X1)
% 3.52/1.00      | k3_tarski(X1) != k1_xboole_0
% 3.52/1.00      | k1_xboole_0 = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2930,plain,
% 3.52/1.00      ( k3_tarski(X0) != k1_xboole_0
% 3.52/1.00      | k1_xboole_0 = X1
% 3.52/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5066,plain,
% 3.52/1.00      ( k1_xboole_0 != X0
% 3.52/1.00      | k1_xboole_0 = X1
% 3.52/1.00      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5,c_2930]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5072,plain,
% 3.52/1.00      ( k1_xboole_0 = X0
% 3.52/1.00      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.00      inference(equality_resolution,[status(thm)],[c_5066]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12020,plain,
% 3.52/1.00      ( sK2(sK5) = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_12012,c_5072]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4146,plain,
% 3.52/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2(sK5)) | sK2(sK5) != X0 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2126]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4148,plain,
% 3.52/1.00      ( v1_xboole_0(sK2(sK5))
% 3.52/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.52/1.00      | sK2(sK5) != k1_xboole_0 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_4146]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_31,plain,
% 3.52/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(sK2(X0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_576,plain,
% 3.52/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(sK2(X0)) | sK5 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_44]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_577,plain,
% 3.52/1.00      ( ~ l1_struct_0(sK5) | ~ v1_xboole_0(sK2(sK5)) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_576]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(contradiction,plain,
% 3.52/1.00      ( $false ),
% 3.52/1.00      inference(minisat,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_12020,c_4148,c_3252,c_662,c_577,c_136,c_43]) ).
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  ------                               Statistics
% 3.52/1.00  
% 3.52/1.00  ------ General
% 3.52/1.00  
% 3.52/1.00  abstr_ref_over_cycles:                  0
% 3.52/1.00  abstr_ref_under_cycles:                 0
% 3.52/1.00  gc_basic_clause_elim:                   0
% 3.52/1.00  forced_gc_time:                         0
% 3.52/1.00  parsing_time:                           0.014
% 3.52/1.00  unif_index_cands_time:                  0.
% 3.52/1.00  unif_index_add_time:                    0.
% 3.52/1.00  orderings_time:                         0.
% 3.52/1.00  out_proof_time:                         0.012
% 3.52/1.00  total_time:                             0.334
% 3.52/1.00  num_of_symbols:                         61
% 3.52/1.00  num_of_terms:                           8790
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing
% 3.52/1.00  
% 3.52/1.00  num_of_splits:                          0
% 3.52/1.00  num_of_split_atoms:                     0
% 3.52/1.00  num_of_reused_defs:                     0
% 3.52/1.00  num_eq_ax_congr_red:                    18
% 3.52/1.00  num_of_sem_filtered_clauses:            1
% 3.52/1.00  num_of_subtypes:                        0
% 3.52/1.00  monotx_restored_types:                  0
% 3.52/1.00  sat_num_of_epr_types:                   0
% 3.52/1.00  sat_num_of_non_cyclic_types:            0
% 3.52/1.00  sat_guarded_non_collapsed_types:        0
% 3.52/1.00  num_pure_diseq_elim:                    0
% 3.52/1.00  simp_replaced_by:                       0
% 3.52/1.00  res_preprocessed:                       207
% 3.52/1.00  prep_upred:                             0
% 3.52/1.00  prep_unflattend:                        108
% 3.52/1.00  smt_new_axioms:                         0
% 3.52/1.00  pred_elim_cands:                        5
% 3.52/1.00  pred_elim:                              5
% 3.52/1.00  pred_elim_cl:                           6
% 3.52/1.00  pred_elim_cycles:                       12
% 3.52/1.00  merged_defs:                            8
% 3.52/1.00  merged_defs_ncl:                        0
% 3.52/1.00  bin_hyper_res:                          8
% 3.52/1.00  prep_cycles:                            4
% 3.52/1.00  pred_elim_time:                         0.022
% 3.52/1.00  splitting_time:                         0.
% 3.52/1.00  sem_filter_time:                        0.
% 3.52/1.00  monotx_time:                            0.001
% 3.52/1.00  subtype_inf_time:                       0.
% 3.52/1.00  
% 3.52/1.00  ------ Problem properties
% 3.52/1.00  
% 3.52/1.00  clauses:                                40
% 3.52/1.00  conjectures:                            4
% 3.52/1.00  epr:                                    2
% 3.52/1.00  horn:                                   33
% 3.52/1.00  ground:                                 8
% 3.52/1.00  unary:                                  14
% 3.52/1.00  binary:                                 10
% 3.52/1.00  lits:                                   88
% 3.52/1.00  lits_eq:                                33
% 3.52/1.00  fd_pure:                                0
% 3.52/1.00  fd_pseudo:                              0
% 3.52/1.00  fd_cond:                                6
% 3.52/1.00  fd_pseudo_cond:                         2
% 3.52/1.00  ac_symbols:                             0
% 3.52/1.00  
% 3.52/1.00  ------ Propositional Solver
% 3.52/1.00  
% 3.52/1.00  prop_solver_calls:                      28
% 3.52/1.00  prop_fast_solver_calls:                 1476
% 3.52/1.00  smt_solver_calls:                       0
% 3.52/1.00  smt_fast_solver_calls:                  0
% 3.52/1.00  prop_num_of_clauses:                    3638
% 3.52/1.00  prop_preprocess_simplified:             11949
% 3.52/1.00  prop_fo_subsumed:                       25
% 3.52/1.00  prop_solver_time:                       0.
% 3.52/1.00  smt_solver_time:                        0.
% 3.52/1.00  smt_fast_solver_time:                   0.
% 3.52/1.00  prop_fast_solver_time:                  0.
% 3.52/1.00  prop_unsat_core_time:                   0.
% 3.52/1.00  
% 3.52/1.00  ------ QBF
% 3.52/1.00  
% 3.52/1.00  qbf_q_res:                              0
% 3.52/1.00  qbf_num_tautologies:                    0
% 3.52/1.00  qbf_prep_cycles:                        0
% 3.52/1.00  
% 3.52/1.00  ------ BMC1
% 3.52/1.00  
% 3.52/1.00  bmc1_current_bound:                     -1
% 3.52/1.00  bmc1_last_solved_bound:                 -1
% 3.52/1.00  bmc1_unsat_core_size:                   -1
% 3.52/1.00  bmc1_unsat_core_parents_size:           -1
% 3.52/1.00  bmc1_merge_next_fun:                    0
% 3.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation
% 3.52/1.00  
% 3.52/1.00  inst_num_of_clauses:                    1230
% 3.52/1.00  inst_num_in_passive:                    703
% 3.52/1.00  inst_num_in_active:                     412
% 3.52/1.00  inst_num_in_unprocessed:                115
% 3.52/1.00  inst_num_of_loops:                      570
% 3.52/1.00  inst_num_of_learning_restarts:          0
% 3.52/1.00  inst_num_moves_active_passive:          156
% 3.52/1.00  inst_lit_activity:                      0
% 3.52/1.00  inst_lit_activity_moves:                0
% 3.52/1.00  inst_num_tautologies:                   0
% 3.52/1.00  inst_num_prop_implied:                  0
% 3.52/1.00  inst_num_existing_simplified:           0
% 3.52/1.00  inst_num_eq_res_simplified:             0
% 3.52/1.00  inst_num_child_elim:                    0
% 3.52/1.00  inst_num_of_dismatching_blockings:      389
% 3.52/1.00  inst_num_of_non_proper_insts:           972
% 3.52/1.00  inst_num_of_duplicates:                 0
% 3.52/1.00  inst_inst_num_from_inst_to_res:         0
% 3.52/1.00  inst_dismatching_checking_time:         0.
% 3.52/1.00  
% 3.52/1.00  ------ Resolution
% 3.52/1.00  
% 3.52/1.00  res_num_of_clauses:                     0
% 3.52/1.00  res_num_in_passive:                     0
% 3.52/1.00  res_num_in_active:                      0
% 3.52/1.00  res_num_of_loops:                       211
% 3.52/1.00  res_forward_subset_subsumed:            60
% 3.52/1.00  res_backward_subset_subsumed:           2
% 3.52/1.00  res_forward_subsumed:                   0
% 3.52/1.00  res_backward_subsumed:                  0
% 3.52/1.00  res_forward_subsumption_resolution:     0
% 3.52/1.00  res_backward_subsumption_resolution:    0
% 3.52/1.00  res_clause_to_clause_subsumption:       265
% 3.52/1.00  res_orphan_elimination:                 0
% 3.52/1.00  res_tautology_del:                      76
% 3.52/1.00  res_num_eq_res_simplified:              0
% 3.52/1.00  res_num_sel_changes:                    0
% 3.52/1.00  res_moves_from_active_to_pass:          0
% 3.52/1.00  
% 3.52/1.00  ------ Superposition
% 3.52/1.00  
% 3.52/1.00  sup_time_total:                         0.
% 3.52/1.00  sup_time_generating:                    0.
% 3.52/1.00  sup_time_sim_full:                      0.
% 3.52/1.00  sup_time_sim_immed:                     0.
% 3.52/1.00  
% 3.52/1.00  sup_num_of_clauses:                     117
% 3.52/1.00  sup_num_in_active:                      76
% 3.52/1.00  sup_num_in_passive:                     41
% 3.52/1.00  sup_num_of_loops:                       112
% 3.52/1.00  sup_fw_superposition:                   55
% 3.52/1.00  sup_bw_superposition:                   84
% 3.52/1.00  sup_immediate_simplified:               43
% 3.52/1.00  sup_given_eliminated:                   1
% 3.52/1.00  comparisons_done:                       0
% 3.52/1.00  comparisons_avoided:                    9
% 3.52/1.00  
% 3.52/1.00  ------ Simplifications
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  sim_fw_subset_subsumed:                 28
% 3.52/1.00  sim_bw_subset_subsumed:                 4
% 3.52/1.00  sim_fw_subsumed:                        1
% 3.52/1.00  sim_bw_subsumed:                        0
% 3.52/1.00  sim_fw_subsumption_res:                 2
% 3.52/1.00  sim_bw_subsumption_res:                 0
% 3.52/1.00  sim_tautology_del:                      3
% 3.52/1.00  sim_eq_tautology_del:                   10
% 3.52/1.00  sim_eq_res_simp:                        0
% 3.52/1.00  sim_fw_demodulated:                     12
% 3.52/1.00  sim_bw_demodulated:                     38
% 3.52/1.00  sim_light_normalised:                   18
% 3.52/1.00  sim_joinable_taut:                      0
% 3.52/1.00  sim_joinable_simp:                      0
% 3.52/1.00  sim_ac_normalised:                      0
% 3.52/1.00  sim_smt_subsumption:                    0
% 3.52/1.00  
%------------------------------------------------------------------------------
