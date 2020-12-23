%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:06 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  244 (1638 expanded)
%              Number of clauses        :  141 ( 462 expanded)
%              Number of leaves         :   33 ( 489 expanded)
%              Depth                    :   22
%              Number of atoms          :  767 (11551 expanded)
%              Number of equality atoms :  319 (3983 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f63,plain,(
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

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f47,f63,f62,f61])).

fof(f111,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f99,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f108,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f113,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f86,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f114,plain,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f85,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f57])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f59])).

fof(f102,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f75])).

fof(f123,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f119])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f77,f75])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f115,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f81,f75])).

fof(f116,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f76,f115])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f53])).

fof(f80,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f82,f75])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2799,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_32,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_45,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_610,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_45])).

cnf(c_611,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_47,negated_conjecture,
    ( l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_615,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_47])).

cnf(c_616,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_2860,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2799,c_611,c_616])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2808,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5158,plain,
    ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2860,c_2808])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2853,plain,
    ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
    inference(light_normalisation,[status(thm)],[c_41,c_611,c_616])).

cnf(c_5351,plain,
    ( k2_struct_0(sK5) = k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_5158,c_2853])).

cnf(c_5363,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_relat_1(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5351,c_2860])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2809,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6103,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_5363,c_2809])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2802,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3760,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
    | k2_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2802])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2798,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2847,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2798,c_611,c_616])).

cnf(c_4169,plain,
    ( k2_struct_0(sK5) = k1_xboole_0
    | k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3760,c_2847])).

cnf(c_4170,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
    | k2_struct_0(sK5) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4169])).

cnf(c_5358,plain,
    ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k2_struct_0(sK4)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5351,c_4170])).

cnf(c_7260,plain,
    ( k2_struct_0(sK4) = k1_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6103,c_5358])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_848,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_40])).

cnf(c_849,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_853,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK6,X0,X1)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_44])).

cnf(c_854,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(renaming,[status(thm)],[c_853])).

cnf(c_2792,plain,
    ( k2_relset_1(X0,X1,sK6) != X1
    | v1_funct_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_3724,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_2792])).

cnf(c_3727,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3724,c_2860,c_2847])).

cnf(c_5359,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),k2_struct_0(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5351,c_3727])).

cnf(c_6250,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(k2_funct_1(sK6)) ),
    inference(superposition,[status(thm)],[c_5359,c_2808])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_886,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_40])).

cnf(c_887,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_889,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_44])).

cnf(c_926,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_889])).

cnf(c_927,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_2791,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_3108,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_3752,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2791,c_42,c_3108])).

cnf(c_6253,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_6250,c_3752])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_776,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_40])).

cnf(c_777,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_781,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK6,X0,X1)
    | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_777,c_44])).

cnf(c_782,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1 ),
    inference(renaming,[status(thm)],[c_781])).

cnf(c_2794,plain,
    ( k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
    | k2_relset_1(X0,X1,sK6) != X1
    | v1_funct_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_3495,plain,
    ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6)
    | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_2794])).

cnf(c_3541,plain,
    ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3495,c_2860,c_2847])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2991,plain,
    ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK4)
    | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
    inference(light_normalisation,[status(thm)],[c_39,c_611,c_616])).

cnf(c_3544,plain,
    ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
    | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK5) ),
    inference(demodulation,[status(thm)],[c_3541,c_2991])).

cnf(c_5360,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
    | k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_5351,c_3544])).

cnf(c_6249,plain,
    ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
    inference(superposition,[status(thm)],[c_5359,c_2809])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_872,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_40])).

cnf(c_873,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_875,plain,
    ( ~ v1_relat_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_44])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_875])).

cnf(c_939,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_2790,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_3111,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_3234,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2790,c_42,c_3111])).

cnf(c_6256,plain,
    ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_6249,c_3234])).

cnf(c_6268,plain,
    ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5360,c_6256])).

cnf(c_7264,plain,
    ( k2_struct_0(sK4) != k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_6253,c_6268])).

cnf(c_8362,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7260,c_7264])).

cnf(c_34,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_584,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_46])).

cnf(c_585,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_587,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_45])).

cnf(c_2796,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_2844,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2796,c_611])).

cnf(c_5365,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_relat_1(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5351,c_2844])).

cnf(c_8379,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8362,c_5365])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2816,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9431,plain,
    ( r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8379,c_2816])).

cnf(c_1969,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4000,plain,
    ( X0 != X1
    | sK2(sK5) != X1
    | sK2(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_6007,plain,
    ( X0 != sK2(sK5)
    | sK2(sK5) = X0
    | sK2(sK5) != sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_4000])).

cnf(c_6008,plain,
    ( sK2(sK5) != sK2(sK5)
    | sK2(sK5) = k1_xboole_0
    | k1_xboole_0 != sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_6007])).

cnf(c_1970,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4965,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK5))
    | sK2(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_4967,plain,
    ( v1_xboole_0(sK2(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4965])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4183,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0))
    | k1_xboole_0 = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4186,plain,
    ( k1_xboole_0 = k1_zfmisc_1(X0)
    | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4183])).

cnf(c_4188,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4186])).

cnf(c_4083,plain,
    ( ~ v1_xboole_0(sK1(X0))
    | k1_xboole_0 = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3127,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X1))
    | X0 != sK1(X1) ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_4078,plain,
    ( ~ v1_xboole_0(sK1(X0))
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK1(X0) ),
    inference(instantiation,[status(thm)],[c_3127])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3394,plain,
    ( ~ r2_hidden(sK2(sK5),X0)
    | k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_3801,plain,
    ( ~ r2_hidden(sK2(sK5),k1_zfmisc_1(X0))
    | k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_3394])).

cnf(c_3803,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5)
    | r2_hidden(sK2(sK5),k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3801])).

cnf(c_3805,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5)
    | r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3803])).

cnf(c_1968,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3439,plain,
    ( sK2(sK5) = sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_1973,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3238,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_3240,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3238])).

cnf(c_15,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_280,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_11])).

cnf(c_2797,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_10,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2839,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2797,c_10])).

cnf(c_3036,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2839])).

cnf(c_3038,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_33,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_595,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_46])).

cnf(c_596,plain,
    ( ~ l1_struct_0(sK5)
    | ~ v1_xboole_0(sK2(sK5)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_153,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_148,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_135,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_123,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_120,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_117,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_9438,plain,
    ( ~ v1_xboole_0(sK1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(grounding,[status(thm)],[c_4083:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_9439,plain,
    ( ~ v1_xboole_0(sK1(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK1(k1_xboole_0) ),
    inference(grounding,[status(thm)],[c_4078:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_9440,plain,
    ( v1_xboole_0(sK1(k1_xboole_0)) ),
    inference(grounding,[status(thm)],[c_13:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9431,c_6008,c_4967,c_4188,c_9438,c_9439,c_3805,c_3439,c_3240,c_3038,c_596,c_153,c_148,c_135,c_9440,c_123,c_120,c_117,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:33:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.63/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.98  
% 3.63/0.98  ------  iProver source info
% 3.63/0.98  
% 3.63/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.98  git: non_committed_changes: false
% 3.63/0.98  git: last_make_outside_of_git: false
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     num_symb
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       true
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  ------ Parsing...
% 3.63/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.98  ------ Proving...
% 3.63/0.98  ------ Problem Properties 
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  clauses                                 42
% 3.63/0.98  conjectures                             4
% 3.63/0.98  EPR                                     5
% 3.63/0.98  Horn                                    34
% 3.63/0.98  unary                                   14
% 3.63/0.98  binary                                  10
% 3.63/0.98  lits                                    94
% 3.63/0.98  lits eq                                 33
% 3.63/0.98  fd_pure                                 0
% 3.63/0.98  fd_pseudo                               0
% 3.63/0.98  fd_cond                                 6
% 3.63/0.98  fd_pseudo_cond                          2
% 3.63/0.98  AC symbols                              0
% 3.63/0.98  
% 3.63/0.98  ------ Schedule dynamic 5 is on 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  Current options:
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     none
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       false
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ Proving...
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS status Theorem for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  fof(f23,conjecture,(
% 3.63/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f24,negated_conjecture,(
% 3.63/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.63/0.98    inference(negated_conjecture,[],[f23])).
% 3.63/0.98  
% 3.63/0.98  fof(f46,plain,(
% 3.63/0.98    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.63/0.98    inference(ennf_transformation,[],[f24])).
% 3.63/0.98  
% 3.63/0.98  fof(f47,plain,(
% 3.63/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.63/0.98    inference(flattening,[],[f46])).
% 3.63/0.98  
% 3.63/0.98  fof(f63,plain,(
% 3.63/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK6)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK6)) != k2_struct_0(X1)) & v2_funct_1(sK6) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK6) = k2_struct_0(X1) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f62,plain,(
% 3.63/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK5),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK5),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK5),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK5),X2)) != k2_struct_0(sK5)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),X2) = k2_struct_0(sK5) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))) )),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f61,plain,(
% 3.63/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(X1),X2)) != k2_struct_0(sK4) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK4))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f64,plain,(
% 3.63/0.98    (((k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4) | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5)) & v2_funct_1(sK6) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)) & l1_struct_0(sK4)),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f47,f63,f62,f61])).
% 3.63/0.98  
% 3.63/0.98  fof(f111,plain,(
% 3.63/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f19,axiom,(
% 3.63/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f40,plain,(
% 3.63/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.63/0.98    inference(ennf_transformation,[],[f19])).
% 3.63/0.98  
% 3.63/0.98  fof(f99,plain,(
% 3.63/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f40])).
% 3.63/0.98  
% 3.63/0.98  fof(f108,plain,(
% 3.63/0.98    l1_struct_0(sK5)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f106,plain,(
% 3.63/0.98    l1_struct_0(sK4)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f16,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f35,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f16])).
% 3.63/0.98  
% 3.63/0.98  fof(f89,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f35])).
% 3.63/0.98  
% 3.63/0.98  fof(f112,plain,(
% 3.63/0.98    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f15,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f34,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f15])).
% 3.63/0.98  
% 3.63/0.98  fof(f88,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f34])).
% 3.63/0.98  
% 3.63/0.98  fof(f17,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f36,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f17])).
% 3.63/0.98  
% 3.63/0.98  fof(f37,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(flattening,[],[f36])).
% 3.63/0.98  
% 3.63/0.98  fof(f56,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(nnf_transformation,[],[f37])).
% 3.63/0.98  
% 3.63/0.98  fof(f90,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f56])).
% 3.63/0.98  
% 3.63/0.98  fof(f110,plain,(
% 3.63/0.98    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f18,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f38,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.63/0.98    inference(ennf_transformation,[],[f18])).
% 3.63/0.98  
% 3.63/0.98  fof(f39,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.63/0.98    inference(flattening,[],[f38])).
% 3.63/0.98  
% 3.63/0.98  fof(f98,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f39])).
% 3.63/0.98  
% 3.63/0.98  fof(f113,plain,(
% 3.63/0.98    v2_funct_1(sK6)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f109,plain,(
% 3.63/0.98    v1_funct_1(sK6)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f14,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f33,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f14])).
% 3.63/0.98  
% 3.63/0.98  fof(f87,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f33])).
% 3.63/0.98  
% 3.63/0.98  fof(f13,axiom,(
% 3.63/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f31,plain,(
% 3.63/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f13])).
% 3.63/0.98  
% 3.63/0.98  fof(f32,plain,(
% 3.63/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.63/0.98    inference(flattening,[],[f31])).
% 3.63/0.98  
% 3.63/0.98  fof(f86,plain,(
% 3.63/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f32])).
% 3.63/0.98  
% 3.63/0.98  fof(f22,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f44,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.63/0.98    inference(ennf_transformation,[],[f22])).
% 3.63/0.98  
% 3.63/0.98  fof(f45,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.63/0.98    inference(flattening,[],[f44])).
% 3.63/0.98  
% 3.63/0.98  fof(f105,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f45])).
% 3.63/0.98  
% 3.63/0.98  fof(f114,plain,(
% 3.63/0.98    k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4) | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f85,plain,(
% 3.63/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f32])).
% 3.63/0.98  
% 3.63/0.98  fof(f20,axiom,(
% 3.63/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f26,plain,(
% 3.63/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.63/0.98    inference(pure_predicate_removal,[],[f20])).
% 3.63/0.98  
% 3.63/0.98  fof(f41,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f26])).
% 3.63/0.98  
% 3.63/0.98  fof(f42,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.63/0.98    inference(flattening,[],[f41])).
% 3.63/0.98  
% 3.63/0.98  fof(f57,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f58,plain,(
% 3.63/0.98    ! [X0] : ((~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f57])).
% 3.63/0.98  
% 3.63/0.98  fof(f100,plain,(
% 3.63/0.98    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f58])).
% 3.63/0.98  
% 3.63/0.98  fof(f107,plain,(
% 3.63/0.98    ~v2_struct_0(sK5)),
% 3.63/0.98    inference(cnf_transformation,[],[f64])).
% 3.63/0.98  
% 3.63/0.98  fof(f4,axiom,(
% 3.63/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f28,plain,(
% 3.63/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f4])).
% 3.63/0.98  
% 3.63/0.98  fof(f52,plain,(
% 3.63/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.63/0.98    inference(nnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f71,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f52])).
% 3.63/0.98  
% 3.63/0.98  fof(f1,axiom,(
% 3.63/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f27,plain,(
% 3.63/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.63/0.98    inference(ennf_transformation,[],[f1])).
% 3.63/0.98  
% 3.63/0.98  fof(f65,plain,(
% 3.63/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f27])).
% 3.63/0.98  
% 3.63/0.98  fof(f21,axiom,(
% 3.63/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f25,plain,(
% 3.63/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 3.63/0.98    inference(rectify,[],[f21])).
% 3.63/0.98  
% 3.63/0.98  fof(f43,plain,(
% 3.63/0.98    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.63/0.98    inference(ennf_transformation,[],[f25])).
% 3.63/0.98  
% 3.63/0.98  fof(f59,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f60,plain,(
% 3.63/0.98    ! [X0] : (((r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f59])).
% 3.63/0.98  
% 3.63/0.98  fof(f102,plain,(
% 3.63/0.98    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 3.63/0.98    inference(cnf_transformation,[],[f60])).
% 3.63/0.98  
% 3.63/0.98  fof(f11,axiom,(
% 3.63/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f29,plain,(
% 3.63/0.98    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f11])).
% 3.63/0.98  
% 3.63/0.98  fof(f55,plain,(
% 3.63/0.98    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/0.98    inference(nnf_transformation,[],[f29])).
% 3.63/0.98  
% 3.63/0.98  fof(f83,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f55])).
% 3.63/0.98  
% 3.63/0.98  fof(f5,axiom,(
% 3.63/0.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f75,plain,(
% 3.63/0.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f5])).
% 3.63/0.98  
% 3.63/0.98  fof(f119,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f83,f75])).
% 3.63/0.98  
% 3.63/0.98  fof(f123,plain,(
% 3.63/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(equality_resolution,[],[f119])).
% 3.63/0.98  
% 3.63/0.98  fof(f7,axiom,(
% 3.63/0.98    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f77,plain,(
% 3.63/0.98    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f7])).
% 3.63/0.98  
% 3.63/0.98  fof(f117,plain,(
% 3.63/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f77,f75])).
% 3.63/0.98  
% 3.63/0.98  fof(f6,axiom,(
% 3.63/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f76,plain,(
% 3.63/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f6])).
% 3.63/0.98  
% 3.63/0.98  fof(f10,axiom,(
% 3.63/0.98    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f81,plain,(
% 3.63/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f10])).
% 3.63/0.98  
% 3.63/0.98  fof(f115,plain,(
% 3.63/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f81,f75])).
% 3.63/0.98  
% 3.63/0.98  fof(f116,plain,(
% 3.63/0.98    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.63/0.98    inference(definition_unfolding,[],[f76,f115])).
% 3.63/0.98  
% 3.63/0.98  fof(f101,plain,(
% 3.63/0.98    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f58])).
% 3.63/0.98  
% 3.63/0.98  fof(f2,axiom,(
% 3.63/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f48,plain,(
% 3.63/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.63/0.98    inference(nnf_transformation,[],[f2])).
% 3.63/0.98  
% 3.63/0.98  fof(f49,plain,(
% 3.63/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.63/0.98    inference(rectify,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  fof(f50,plain,(
% 3.63/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f51,plain,(
% 3.63/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 3.63/0.98  
% 3.63/0.98  fof(f67,plain,(
% 3.63/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.63/0.98    inference(cnf_transformation,[],[f51])).
% 3.63/0.98  
% 3.63/0.98  fof(f121,plain,(
% 3.63/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.63/0.98    inference(equality_resolution,[],[f67])).
% 3.63/0.98  
% 3.63/0.98  fof(f3,axiom,(
% 3.63/0.98    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f70,plain,(
% 3.63/0.98    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f3])).
% 3.63/0.98  
% 3.63/0.98  fof(f9,axiom,(
% 3.63/0.98    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f53,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f54,plain,(
% 3.63/0.98    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f53])).
% 3.63/0.98  
% 3.63/0.98  fof(f80,plain,(
% 3.63/0.98    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f54])).
% 3.63/0.98  
% 3.63/0.98  fof(f82,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f55])).
% 3.63/0.98  
% 3.63/0.98  fof(f120,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f82,f75])).
% 3.63/0.98  
% 3.63/0.98  fof(f12,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f30,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.63/0.98    inference(ennf_transformation,[],[f12])).
% 3.63/0.98  
% 3.63/0.98  fof(f84,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f30])).
% 3.63/0.98  
% 3.63/0.98  cnf(c_42,negated_conjecture,
% 3.63/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2799,plain,
% 3.63/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_32,plain,
% 3.63/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_45,negated_conjecture,
% 3.63/0.98      ( l1_struct_0(sK5) ),
% 3.63/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_610,plain,
% 3.63/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK5 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_45]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_611,plain,
% 3.63/0.98      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_610]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_47,negated_conjecture,
% 3.63/0.98      ( l1_struct_0(sK4) ),
% 3.63/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_615,plain,
% 3.63/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_47]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_616,plain,
% 3.63/0.98      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_615]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2860,plain,
% 3.63/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) = iProver_top ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_2799,c_611,c_616]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_22,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2808,plain,
% 3.63/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.63/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5158,plain,
% 3.63/0.98      ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2860,c_2808]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_41,negated_conjecture,
% 3.63/0.98      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
% 3.63/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2853,plain,
% 3.63/0.98      ( k2_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK5) ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_41,c_611,c_616]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5351,plain,
% 3.63/0.98      ( k2_struct_0(sK5) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_5158,c_2853]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5363,plain,
% 3.63/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_relat_1(sK6)))) = iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_5351,c_2860]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_21,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2809,plain,
% 3.63/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.63/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6103,plain,
% 3.63/0.98      ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_5363,c_2809]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_28,plain,
% 3.63/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.98      | k1_xboole_0 = X2 ),
% 3.63/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2802,plain,
% 3.63/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.63/0.98      | k1_xboole_0 = X1
% 3.63/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.63/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3760,plain,
% 3.63/0.98      ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
% 3.63/0.98      | k2_struct_0(sK5) = k1_xboole_0
% 3.63/0.98      | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2860,c_2802]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_43,negated_conjecture,
% 3.63/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2798,plain,
% 3.63/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2847,plain,
% 3.63/0.98      ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) = iProver_top ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_2798,c_611,c_616]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4169,plain,
% 3.63/0.98      ( k2_struct_0(sK5) = k1_xboole_0
% 3.63/0.98      | k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_3760,c_2847]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4170,plain,
% 3.63/0.98      ( k1_relset_1(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_struct_0(sK4)
% 3.63/0.98      | k2_struct_0(sK5) = k1_xboole_0 ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_4169]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5358,plain,
% 3.63/0.98      ( k1_relset_1(k2_struct_0(sK4),k2_relat_1(sK6),sK6) = k2_struct_0(sK4)
% 3.63/0.98      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_5351,c_4170]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7260,plain,
% 3.63/0.98      ( k2_struct_0(sK4) = k1_relat_1(sK6)
% 3.63/0.98      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_6103,c_5358]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_29,plain,
% 3.63/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | ~ v2_funct_1(X0)
% 3.63/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.63/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_40,negated_conjecture,
% 3.63/0.98      ( v2_funct_1(sK6) ),
% 3.63/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_848,plain,
% 3.63/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.63/0.98      | sK6 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_40]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_849,plain,
% 3.63/0.98      ( ~ v1_funct_2(sK6,X0,X1)
% 3.63/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.63/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | ~ v1_funct_1(sK6)
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_848]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_44,negated_conjecture,
% 3.63/0.98      ( v1_funct_1(sK6) ),
% 3.63/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_853,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.63/0.98      | ~ v1_funct_2(sK6,X0,X1)
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_849,c_44]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_854,plain,
% 3.63/0.98      ( ~ v1_funct_2(sK6,X0,X1)
% 3.63/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.63/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_853]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2792,plain,
% 3.63/0.98      ( k2_relset_1(X0,X1,sK6) != X1
% 3.63/0.98      | v1_funct_2(sK6,X0,X1) != iProver_top
% 3.63/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.63/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3724,plain,
% 3.63/0.98      ( v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 3.63/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top
% 3.63/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2853,c_2792]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3727,plain,
% 3.63/0.98      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK4)))) = iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_3724,c_2860,c_2847]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5359,plain,
% 3.63/0.98      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),k2_struct_0(sK4)))) = iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_5351,c_3727]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6250,plain,
% 3.63/0.98      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(k2_funct_1(sK6)) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_5359,c_2808]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_20,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | v1_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_18,plain,
% 3.63/0.98      ( ~ v1_relat_1(X0)
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | ~ v2_funct_1(X0)
% 3.63/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_886,plain,
% 3.63/0.98      ( ~ v1_relat_1(X0)
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.63/0.98      | sK6 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_40]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_887,plain,
% 3.63/0.98      ( ~ v1_relat_1(sK6)
% 3.63/0.98      | ~ v1_funct_1(sK6)
% 3.63/0.98      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_886]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_889,plain,
% 3.63/0.98      ( ~ v1_relat_1(sK6)
% 3.63/0.98      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_887,c_44]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_926,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
% 3.63/0.98      | sK6 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_889]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_927,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_926]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2791,plain,
% 3.63/0.98      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
% 3.63/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3108,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 3.63/0.98      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_927]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3752,plain,
% 3.63/0.98      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_2791,c_42,c_3108]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6253,plain,
% 3.63/0.98      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_6250,c_3752]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_38,plain,
% 3.63/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | ~ v2_funct_1(X0)
% 3.63/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.63/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.63/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_776,plain,
% 3.63/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.63/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.63/0.98      | sK6 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_38,c_40]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_777,plain,
% 3.63/0.98      ( ~ v1_funct_2(sK6,X0,X1)
% 3.63/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | ~ v1_funct_1(sK6)
% 3.63/0.98      | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_776]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_781,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | ~ v1_funct_2(sK6,X0,X1)
% 3.63/0.98      | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_777,c_44]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_782,plain,
% 3.63/0.98      ( ~ v1_funct_2(sK6,X0,X1)
% 3.63/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1 ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_781]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2794,plain,
% 3.63/0.98      ( k2_tops_2(X0,X1,sK6) = k2_funct_1(sK6)
% 3.63/0.98      | k2_relset_1(X0,X1,sK6) != X1
% 3.63/0.98      | v1_funct_2(sK6,X0,X1) != iProver_top
% 3.63/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3495,plain,
% 3.63/0.98      ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6)
% 3.63/0.98      | v1_funct_2(sK6,k2_struct_0(sK4),k2_struct_0(sK5)) != iProver_top
% 3.63/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK4),k2_struct_0(sK5)))) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2853,c_2794]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3541,plain,
% 3.63/0.98      ( k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6) = k2_funct_1(sK6) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_3495,c_2860,c_2847]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_39,negated_conjecture,
% 3.63/0.98      ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK4)
% 3.63/0.98      | k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
% 3.63/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2991,plain,
% 3.63/0.98      ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK4)
% 3.63/0.98      | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_tops_2(k2_struct_0(sK4),k2_struct_0(sK5),sK6)) != k2_struct_0(sK5) ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_39,c_611,c_616]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3544,plain,
% 3.63/0.98      ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
% 3.63/0.98      | k1_relset_1(k2_struct_0(sK5),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK5) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_3541,c_2991]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5360,plain,
% 3.63/0.98      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4)
% 3.63/0.98      | k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_relat_1(sK6) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_5351,c_3544]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6249,plain,
% 3.63/0.98      ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_5359,c_2809]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_19,plain,
% 3.63/0.98      ( ~ v1_relat_1(X0)
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | ~ v2_funct_1(X0)
% 3.63/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_872,plain,
% 3.63/0.98      ( ~ v1_relat_1(X0)
% 3.63/0.98      | ~ v1_funct_1(X0)
% 3.63/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.63/0.98      | sK6 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_40]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_873,plain,
% 3.63/0.98      ( ~ v1_relat_1(sK6)
% 3.63/0.98      | ~ v1_funct_1(sK6)
% 3.63/0.98      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_872]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_875,plain,
% 3.63/0.98      ( ~ v1_relat_1(sK6)
% 3.63/0.98      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_873,c_44]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_938,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
% 3.63/0.98      | sK6 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_875]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_939,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.63/0.98      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_938]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2790,plain,
% 3.63/0.98      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
% 3.63/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3111,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 3.63/0.98      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_939]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3234,plain,
% 3.63/0.98      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_2790,c_42,c_3111]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6256,plain,
% 3.63/0.98      ( k1_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_6249,c_3234]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6268,plain,
% 3.63/0.98      ( k2_relset_1(k2_relat_1(sK6),k2_struct_0(sK4),k2_funct_1(sK6)) != k2_struct_0(sK4) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_5360,c_6256]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7264,plain,
% 3.63/0.98      ( k2_struct_0(sK4) != k1_relat_1(sK6) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_6253,c_6268]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8362,plain,
% 3.63/0.98      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_7260,c_7264]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_34,plain,
% 3.63/0.98      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.63/0.98      | v2_struct_0(X0)
% 3.63/0.98      | ~ l1_struct_0(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_46,negated_conjecture,
% 3.63/0.98      ( ~ v2_struct_0(sK5) ),
% 3.63/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_584,plain,
% 3.63/0.98      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.63/0.98      | ~ l1_struct_0(X0)
% 3.63/0.98      | sK5 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_46]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_585,plain,
% 3.63/0.98      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.63/0.98      | ~ l1_struct_0(sK5) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_584]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_587,plain,
% 3.63/0.98      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_585,c_45]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2796,plain,
% 3.63/0.98      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2844,plain,
% 3.63/0.98      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_2796,c_611]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5365,plain,
% 3.63/0.98      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k2_relat_1(sK6))) = iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_5351,c_2844]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8379,plain,
% 3.63/0.98      ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_8362,c_5365]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2816,plain,
% 3.63/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.63/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.63/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9431,plain,
% 3.63/0.98      ( r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.63/0.98      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_8379,c_2816]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1969,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4000,plain,
% 3.63/0.98      ( X0 != X1 | sK2(sK5) != X1 | sK2(sK5) = X0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_1969]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6007,plain,
% 3.63/0.98      ( X0 != sK2(sK5) | sK2(sK5) = X0 | sK2(sK5) != sK2(sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_4000]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6008,plain,
% 3.63/0.98      ( sK2(sK5) != sK2(sK5)
% 3.63/0.98      | sK2(sK5) = k1_xboole_0
% 3.63/0.98      | k1_xboole_0 != sK2(sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_6007]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1970,plain,
% 3.63/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.63/0.98      theory(equality) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4965,plain,
% 3.63/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2(sK5)) | sK2(sK5) != X0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_1970]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4967,plain,
% 3.63/0.98      ( v1_xboole_0(sK2(sK5))
% 3.63/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.63/0.98      | sK2(sK5) != k1_xboole_0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_4965]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_0,plain,
% 3.63/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4183,plain,
% 3.63/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) | k1_xboole_0 = k1_zfmisc_1(X0) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4186,plain,
% 3.63/0.98      ( k1_xboole_0 = k1_zfmisc_1(X0)
% 3.63/0.98      | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_4183]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4188,plain,
% 3.63/0.98      ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
% 3.63/0.98      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_4186]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4083,plain,
% 3.63/0.98      ( ~ v1_xboole_0(sK1(X0)) | k1_xboole_0 = sK1(X0) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3127,plain,
% 3.63/0.98      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK1(X1)) | X0 != sK1(X1) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_1970]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4078,plain,
% 3.63/0.98      ( ~ v1_xboole_0(sK1(X0))
% 3.63/0.98      | v1_xboole_0(k1_xboole_0)
% 3.63/0.98      | k1_xboole_0 != sK1(X0) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3127]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_37,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,X1)
% 3.63/0.98      | k3_tarski(X1) != k1_xboole_0
% 3.63/0.98      | k1_xboole_0 = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3394,plain,
% 3.63/0.98      ( ~ r2_hidden(sK2(sK5),X0)
% 3.63/0.98      | k3_tarski(X0) != k1_xboole_0
% 3.63/0.98      | k1_xboole_0 = sK2(sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_37]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3801,plain,
% 3.63/0.98      ( ~ r2_hidden(sK2(sK5),k1_zfmisc_1(X0))
% 3.63/0.98      | k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
% 3.63/0.98      | k1_xboole_0 = sK2(sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3394]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3803,plain,
% 3.63/0.98      ( k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
% 3.63/0.98      | k1_xboole_0 = sK2(sK5)
% 3.63/0.98      | r2_hidden(sK2(sK5),k1_zfmisc_1(X0)) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_3801]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3805,plain,
% 3.63/0.98      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
% 3.63/0.98      | k1_xboole_0 = sK2(sK5)
% 3.63/0.98      | r2_hidden(sK2(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3803]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1968,plain,( X0 = X0 ),theory(equality) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3439,plain,
% 3.63/0.98      ( sK2(sK5) = sK2(sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_1968]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1973,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.63/0.98      theory(equality) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3238,plain,
% 3.63/0.98      ( r2_hidden(X0,X1)
% 3.63/0.98      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 3.63/0.98      | X0 != X2
% 3.63/0.98      | X1 != k1_zfmisc_1(X3) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_1973]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3240,plain,
% 3.63/0.98      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.98      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.63/0.98      | k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
% 3.63/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3238]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15,plain,
% 3.63/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 3.63/0.98      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f123]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_11,plain,
% 3.63/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_280,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_15,c_11]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2797,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_10,plain,
% 3.63/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2839,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_2797,c_10]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3036,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.63/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2839]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3038,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3036]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_33,plain,
% 3.63/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(sK2(X0)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_595,plain,
% 3.63/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(sK2(X0)) | sK5 != X0 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_33,c_46]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_596,plain,
% 3.63/0.98      ( ~ l1_struct_0(sK5) | ~ v1_xboole_0(sK2(sK5)) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_595]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3,plain,
% 3.63/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_153,plain,
% 3.63/0.98      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5,plain,
% 3.63/0.98      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_148,plain,
% 3.63/0.98      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_135,plain,
% 3.63/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_13,plain,
% 3.63/0.98      ( v1_xboole_0(sK1(X0)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_123,plain,
% 3.63/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.98      | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_16,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.98      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 3.63/0.98      | k1_xboole_0 = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_120,plain,
% 3.63/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.98      | ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0))
% 3.63/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_17,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.98      | ~ r2_hidden(X2,X0)
% 3.63/0.98      | ~ v1_xboole_0(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_117,plain,
% 3.63/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.63/0.98      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.63/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9438,plain,
% 3.63/0.98      ( ~ v1_xboole_0(sK1(k1_xboole_0))
% 3.63/0.98      | k1_xboole_0 = sK1(k1_xboole_0) ),
% 3.63/0.98      inference(grounding,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_4083:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9439,plain,
% 3.63/0.98      ( ~ v1_xboole_0(sK1(k1_xboole_0))
% 3.63/0.98      | v1_xboole_0(k1_xboole_0)
% 3.63/0.98      | k1_xboole_0 != sK1(k1_xboole_0) ),
% 3.63/0.98      inference(grounding,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_4078:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9440,plain,
% 3.63/0.98      ( v1_xboole_0(sK1(k1_xboole_0)) ),
% 3.63/0.98      inference(grounding,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_13:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(contradiction,plain,
% 3.63/0.98      ( $false ),
% 3.63/0.98      inference(minisat,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_9431,c_6008,c_4967,c_4188,c_9438,c_9439,c_3805,c_3439,
% 3.63/0.98                 c_3240,c_3038,c_596,c_153,c_148,c_135,c_9440,c_123,
% 3.63/0.98                 c_120,c_117,c_45]) ).
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  ------                               Statistics
% 3.63/0.98  
% 3.63/0.98  ------ General
% 3.63/0.98  
% 3.63/0.98  abstr_ref_over_cycles:                  0
% 3.63/0.98  abstr_ref_under_cycles:                 0
% 3.63/0.98  gc_basic_clause_elim:                   0
% 3.63/0.98  forced_gc_time:                         0
% 3.63/0.98  parsing_time:                           0.01
% 3.63/0.98  unif_index_cands_time:                  0.
% 3.63/0.98  unif_index_add_time:                    0.
% 3.63/0.98  orderings_time:                         0.
% 3.63/0.98  out_proof_time:                         0.01
% 3.63/0.98  total_time:                             0.343
% 3.63/0.98  num_of_symbols:                         61
% 3.63/0.98  num_of_terms:                           6907
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing
% 3.63/0.98  
% 3.63/0.98  num_of_splits:                          0
% 3.63/0.98  num_of_split_atoms:                     0
% 3.63/0.98  num_of_reused_defs:                     0
% 3.63/0.98  num_eq_ax_congr_red:                    18
% 3.63/0.98  num_of_sem_filtered_clauses:            1
% 3.63/0.98  num_of_subtypes:                        0
% 3.63/0.98  monotx_restored_types:                  0
% 3.63/0.98  sat_num_of_epr_types:                   0
% 3.63/0.98  sat_num_of_non_cyclic_types:            0
% 3.63/0.98  sat_guarded_non_collapsed_types:        0
% 3.63/0.98  num_pure_diseq_elim:                    0
% 3.63/0.98  simp_replaced_by:                       0
% 3.63/0.98  res_preprocessed:                       215
% 3.63/0.98  prep_upred:                             0
% 3.63/0.98  prep_unflattend:                        96
% 3.63/0.98  smt_new_axioms:                         0
% 3.63/0.98  pred_elim_cands:                        5
% 3.63/0.98  pred_elim:                              5
% 3.63/0.98  pred_elim_cl:                           6
% 3.63/0.98  pred_elim_cycles:                       10
% 3.63/0.98  merged_defs:                            8
% 3.63/0.98  merged_defs_ncl:                        0
% 3.63/0.98  bin_hyper_res:                          8
% 3.63/0.98  prep_cycles:                            4
% 3.63/0.98  pred_elim_time:                         0.021
% 3.63/0.98  splitting_time:                         0.
% 3.63/0.98  sem_filter_time:                        0.
% 3.63/0.98  monotx_time:                            0.001
% 3.63/0.98  subtype_inf_time:                       0.
% 3.63/0.98  
% 3.63/0.98  ------ Problem properties
% 3.63/0.98  
% 3.63/0.98  clauses:                                42
% 3.63/0.98  conjectures:                            4
% 3.63/0.98  epr:                                    5
% 3.63/0.98  horn:                                   34
% 3.63/0.98  ground:                                 8
% 3.63/0.98  unary:                                  14
% 3.63/0.98  binary:                                 10
% 3.63/0.98  lits:                                   94
% 3.63/0.98  lits_eq:                                33
% 3.63/0.98  fd_pure:                                0
% 3.63/0.98  fd_pseudo:                              0
% 3.63/0.98  fd_cond:                                6
% 3.63/0.98  fd_pseudo_cond:                         2
% 3.63/0.98  ac_symbols:                             0
% 3.63/0.98  
% 3.63/0.98  ------ Propositional Solver
% 3.63/0.98  
% 3.63/0.98  prop_solver_calls:                      27
% 3.63/0.98  prop_fast_solver_calls:                 1441
% 3.63/0.98  smt_solver_calls:                       0
% 3.63/0.98  smt_fast_solver_calls:                  0
% 3.63/0.98  prop_num_of_clauses:                    3088
% 3.63/0.98  prop_preprocess_simplified:             10046
% 3.63/0.98  prop_fo_subsumed:                       24
% 3.63/0.98  prop_solver_time:                       0.
% 3.63/0.98  smt_solver_time:                        0.
% 3.63/0.98  smt_fast_solver_time:                   0.
% 3.63/0.98  prop_fast_solver_time:                  0.
% 3.63/0.98  prop_unsat_core_time:                   0.
% 3.63/0.98  
% 3.63/0.98  ------ QBF
% 3.63/0.98  
% 3.63/0.98  qbf_q_res:                              0
% 3.63/0.98  qbf_num_tautologies:                    0
% 3.63/0.98  qbf_prep_cycles:                        0
% 3.63/0.98  
% 3.63/0.98  ------ BMC1
% 3.63/0.98  
% 3.63/0.98  bmc1_current_bound:                     -1
% 3.63/0.98  bmc1_last_solved_bound:                 -1
% 3.63/0.98  bmc1_unsat_core_size:                   -1
% 3.63/0.98  bmc1_unsat_core_parents_size:           -1
% 3.63/0.98  bmc1_merge_next_fun:                    0
% 3.63/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation
% 3.63/0.98  
% 3.63/0.98  inst_num_of_clauses:                    1014
% 3.63/0.98  inst_num_in_passive:                    214
% 3.63/0.98  inst_num_in_active:                     382
% 3.63/0.98  inst_num_in_unprocessed:                420
% 3.63/0.98  inst_num_of_loops:                      450
% 3.63/0.98  inst_num_of_learning_restarts:          0
% 3.63/0.98  inst_num_moves_active_passive:          66
% 3.63/0.98  inst_lit_activity:                      0
% 3.63/0.98  inst_lit_activity_moves:                0
% 3.63/0.98  inst_num_tautologies:                   0
% 3.63/0.98  inst_num_prop_implied:                  0
% 3.63/0.98  inst_num_existing_simplified:           0
% 3.63/0.98  inst_num_eq_res_simplified:             0
% 3.63/0.98  inst_num_child_elim:                    0
% 3.63/0.98  inst_num_of_dismatching_blockings:      213
% 3.63/0.98  inst_num_of_non_proper_insts:           695
% 3.63/0.98  inst_num_of_duplicates:                 0
% 3.63/0.98  inst_inst_num_from_inst_to_res:         0
% 3.63/0.98  inst_dismatching_checking_time:         0.
% 3.63/0.98  
% 3.63/0.98  ------ Resolution
% 3.63/0.98  
% 3.63/0.98  res_num_of_clauses:                     0
% 3.63/0.98  res_num_in_passive:                     0
% 3.63/0.98  res_num_in_active:                      0
% 3.63/0.98  res_num_of_loops:                       219
% 3.63/0.98  res_forward_subset_subsumed:            64
% 3.63/0.98  res_backward_subset_subsumed:           6
% 3.63/0.98  res_forward_subsumed:                   0
% 3.63/0.98  res_backward_subsumed:                  0
% 3.63/0.98  res_forward_subsumption_resolution:     0
% 3.63/0.98  res_backward_subsumption_resolution:    0
% 3.63/0.98  res_clause_to_clause_subsumption:       226
% 3.63/0.98  res_orphan_elimination:                 0
% 3.63/0.98  res_tautology_del:                      57
% 3.63/0.98  res_num_eq_res_simplified:              0
% 3.63/0.98  res_num_sel_changes:                    0
% 3.63/0.98  res_moves_from_active_to_pass:          0
% 3.63/0.98  
% 3.63/0.98  ------ Superposition
% 3.63/0.98  
% 3.63/0.98  sup_time_total:                         0.
% 3.63/0.98  sup_time_generating:                    0.
% 3.63/0.98  sup_time_sim_full:                      0.
% 3.63/0.98  sup_time_sim_immed:                     0.
% 3.63/0.98  
% 3.63/0.98  sup_num_of_clauses:                     99
% 3.63/0.98  sup_num_in_active:                      53
% 3.63/0.98  sup_num_in_passive:                     46
% 3.63/0.98  sup_num_of_loops:                       89
% 3.63/0.98  sup_fw_superposition:                   41
% 3.63/0.98  sup_bw_superposition:                   50
% 3.63/0.98  sup_immediate_simplified:               26
% 3.63/0.98  sup_given_eliminated:                   0
% 3.63/0.98  comparisons_done:                       0
% 3.63/0.98  comparisons_avoided:                    9
% 3.63/0.98  
% 3.63/0.98  ------ Simplifications
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  sim_fw_subset_subsumed:                 20
% 3.63/0.98  sim_bw_subset_subsumed:                 1
% 3.63/0.98  sim_fw_subsumed:                        1
% 3.63/0.98  sim_bw_subsumed:                        0
% 3.63/0.98  sim_fw_subsumption_res:                 1
% 3.63/0.98  sim_bw_subsumption_res:                 0
% 3.63/0.98  sim_tautology_del:                      4
% 3.63/0.98  sim_eq_tautology_del:                   7
% 3.63/0.98  sim_eq_res_simp:                        0
% 3.63/0.98  sim_fw_demodulated:                     3
% 3.63/0.98  sim_bw_demodulated:                     37
% 3.63/0.98  sim_light_normalised:                   11
% 3.63/0.98  sim_joinable_taut:                      0
% 3.63/0.98  sim_joinable_simp:                      0
% 3.63/0.98  sim_ac_normalised:                      0
% 3.63/0.98  sim_smt_subsumption:                    0
% 3.63/0.98  
%------------------------------------------------------------------------------
