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
% DateTime   : Thu Dec  3 12:17:07 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  189 (2245 expanded)
%              Number of clauses        :  115 ( 620 expanded)
%              Number of leaves         :   25 ( 682 expanded)
%              Depth                    :   23
%              Number of atoms          :  593 (16378 expanded)
%              Number of equality atoms :  273 (5683 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X1) )
        & v2_funct_1(sK4)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
            ( ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(sK3) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_struct_0(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(sK2)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) )
    & v2_funct_1(sK4)
    & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f46,f45,f44])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f40])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k3_tarski(X0) != k1_xboole_0 )
      & ~ ( k3_tarski(X0) = k1_xboole_0
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k3_tarski(X0) != k1_xboole_0 )
      & ~ ( k3_tarski(X0) = k1_xboole_0
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k3_tarski(X0) = k1_xboole_0 )
      & ( k3_tarski(X0) != k1_xboole_0
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK1(X0),X0)
        & k1_xboole_0 != sK1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK1(X0),X0)
          & k1_xboole_0 != sK1(X0) )
        | k3_tarski(X0) = k1_xboole_0 )
      & ( k3_tarski(X0) != k1_xboole_0
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f42])).

fof(f70,plain,(
    ! [X2,X0] :
      ( k3_tarski(X0) != k1_xboole_0
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1215,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_399,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_400,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_404,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_405,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_1254,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1215,c_400,c_405])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1225,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1907,plain,
    ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1254,c_1225])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1251,plain,
    ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_30,c_400,c_405])).

cnf(c_2036,plain,
    ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_1907,c_1251])).

cnf(c_2433,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2036,c_1254])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1219,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3378,plain,
    ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_struct_0(sK2)
    | k2_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_1219])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1226,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2184,plain,
    ( k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1254,c_1226])).

cnf(c_2720,plain,
    ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2184,c_2036])).

cnf(c_3382,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4)
    | k2_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3378,c_2720])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1214,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1248,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1214,c_400,c_405])).

cnf(c_2434,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2036,c_1248])).

cnf(c_3668,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | k2_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3382,c_2434])).

cnf(c_3669,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3668])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_454,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_458,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK4,X0,X1)
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_33])).

cnf(c_459,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_1210,plain,
    ( k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1781,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1210])).

cnf(c_1784,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1781,c_1254,c_1248])).

cnf(c_2432,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_funct_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2036,c_1784])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1218,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4037,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_1218])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4368,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4037,c_40,c_2433,c_2434])).

cnf(c_4377,plain,
    ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4368,c_1225])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_491,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_492,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_494,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_33])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_494])).

cnf(c_517,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_1209,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_1442,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1900,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_31,c_1442])).

cnf(c_4386,plain,
    ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_4377,c_1900])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1345,plain,
    ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_28,c_400,c_405])).

cnf(c_1787,plain,
    ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_1784,c_1345])).

cnf(c_2431,plain,
    ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2036,c_1787])).

cnf(c_4447,plain,
    ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k2_struct_0(sK2) != k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4386,c_2431])).

cnf(c_4376,plain,
    ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4368,c_1226])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_477,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_478,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_33])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_480])).

cnf(c_529,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_1208,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1858,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_31,c_1445])).

cnf(c_4389,plain,
    ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_4376,c_1858])).

cnf(c_4563,plain,
    ( k2_struct_0(sK2) != k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4447,c_4389])).

cnf(c_4566,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3669,c_4563])).

cnf(c_20,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_373,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_374,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_376,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_34])).

cnf(c_1212,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_1245,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1212,c_400])).

cnf(c_2435,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2036,c_1245])).

cnf(c_4581,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4566,c_2435])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_4,c_23])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_tarski(k1_zfmisc_1(X1)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_2592,plain,
    ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0))
    | k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
    | k1_xboole_0 = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_2599,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
    | k1_xboole_0 = sK0(sK3)
    | m1_subset_1(sK0(sK3),k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2592])).

cnf(c_2601,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK0(sK3)
    | m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_761,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1624,plain,
    ( X0 != X1
    | sK0(sK3) != X1
    | sK0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1884,plain,
    ( X0 != sK0(sK3)
    | sK0(sK3) = X0
    | sK0(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1886,plain,
    ( sK0(sK3) != sK0(sK3)
    | sK0(sK3) = k1_xboole_0
    | k1_xboole_0 != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_760,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1882,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_776,plain,
    ( X0 != X1
    | sK0(X0) = sK0(X1) ),
    theory(equality)).

cnf(c_1626,plain,
    ( sK0(sK3) = sK0(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1881,plain,
    ( sK0(sK3) = sK0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_765,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1476,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0(sK3))
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1478,plain,
    ( v1_xboole_0(sK0(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_384,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_385,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_0,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_115,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_105,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4581,c_2601,c_1886,c_1882,c_1881,c_1478,c_385,c_115,c_5,c_107,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.06/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.00  
% 3.06/1.00  ------  iProver source info
% 3.06/1.00  
% 3.06/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.00  git: non_committed_changes: false
% 3.06/1.00  git: last_make_outside_of_git: false
% 3.06/1.00  
% 3.06/1.00  ------ 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options
% 3.06/1.00  
% 3.06/1.00  --out_options                           all
% 3.06/1.00  --tptp_safe_out                         true
% 3.06/1.00  --problem_path                          ""
% 3.06/1.00  --include_path                          ""
% 3.06/1.00  --clausifier                            res/vclausify_rel
% 3.06/1.00  --clausifier_options                    --mode clausify
% 3.06/1.00  --stdin                                 false
% 3.06/1.00  --stats_out                             all
% 3.06/1.00  
% 3.06/1.00  ------ General Options
% 3.06/1.00  
% 3.06/1.00  --fof                                   false
% 3.06/1.00  --time_out_real                         305.
% 3.06/1.00  --time_out_virtual                      -1.
% 3.06/1.00  --symbol_type_check                     false
% 3.06/1.00  --clausify_out                          false
% 3.06/1.00  --sig_cnt_out                           false
% 3.06/1.00  --trig_cnt_out                          false
% 3.06/1.00  --trig_cnt_out_tolerance                1.
% 3.06/1.00  --trig_cnt_out_sk_spl                   false
% 3.06/1.00  --abstr_cl_out                          false
% 3.06/1.00  
% 3.06/1.00  ------ Global Options
% 3.06/1.00  
% 3.06/1.00  --schedule                              default
% 3.06/1.00  --add_important_lit                     false
% 3.06/1.00  --prop_solver_per_cl                    1000
% 3.06/1.00  --min_unsat_core                        false
% 3.06/1.00  --soft_assumptions                      false
% 3.06/1.00  --soft_lemma_size                       3
% 3.06/1.00  --prop_impl_unit_size                   0
% 3.06/1.00  --prop_impl_unit                        []
% 3.06/1.00  --share_sel_clauses                     true
% 3.06/1.00  --reset_solvers                         false
% 3.06/1.00  --bc_imp_inh                            [conj_cone]
% 3.06/1.00  --conj_cone_tolerance                   3.
% 3.06/1.00  --extra_neg_conj                        none
% 3.06/1.00  --large_theory_mode                     true
% 3.06/1.00  --prolific_symb_bound                   200
% 3.06/1.00  --lt_threshold                          2000
% 3.06/1.00  --clause_weak_htbl                      true
% 3.06/1.00  --gc_record_bc_elim                     false
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing Options
% 3.06/1.00  
% 3.06/1.00  --preprocessing_flag                    true
% 3.06/1.00  --time_out_prep_mult                    0.1
% 3.06/1.00  --splitting_mode                        input
% 3.06/1.00  --splitting_grd                         true
% 3.06/1.00  --splitting_cvd                         false
% 3.06/1.00  --splitting_cvd_svl                     false
% 3.06/1.00  --splitting_nvd                         32
% 3.06/1.00  --sub_typing                            true
% 3.06/1.00  --prep_gs_sim                           true
% 3.06/1.00  --prep_unflatten                        true
% 3.06/1.00  --prep_res_sim                          true
% 3.06/1.00  --prep_upred                            true
% 3.06/1.00  --prep_sem_filter                       exhaustive
% 3.06/1.00  --prep_sem_filter_out                   false
% 3.06/1.00  --pred_elim                             true
% 3.06/1.00  --res_sim_input                         true
% 3.06/1.00  --eq_ax_congr_red                       true
% 3.06/1.00  --pure_diseq_elim                       true
% 3.06/1.00  --brand_transform                       false
% 3.06/1.00  --non_eq_to_eq                          false
% 3.06/1.00  --prep_def_merge                        true
% 3.06/1.00  --prep_def_merge_prop_impl              false
% 3.06/1.00  --prep_def_merge_mbd                    true
% 3.06/1.00  --prep_def_merge_tr_red                 false
% 3.06/1.00  --prep_def_merge_tr_cl                  false
% 3.06/1.00  --smt_preprocessing                     true
% 3.06/1.00  --smt_ac_axioms                         fast
% 3.06/1.00  --preprocessed_out                      false
% 3.06/1.00  --preprocessed_stats                    false
% 3.06/1.00  
% 3.06/1.00  ------ Abstraction refinement Options
% 3.06/1.00  
% 3.06/1.00  --abstr_ref                             []
% 3.06/1.00  --abstr_ref_prep                        false
% 3.06/1.00  --abstr_ref_until_sat                   false
% 3.06/1.00  --abstr_ref_sig_restrict                funpre
% 3.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.00  --abstr_ref_under                       []
% 3.06/1.00  
% 3.06/1.00  ------ SAT Options
% 3.06/1.00  
% 3.06/1.00  --sat_mode                              false
% 3.06/1.00  --sat_fm_restart_options                ""
% 3.06/1.00  --sat_gr_def                            false
% 3.06/1.00  --sat_epr_types                         true
% 3.06/1.00  --sat_non_cyclic_types                  false
% 3.06/1.00  --sat_finite_models                     false
% 3.06/1.00  --sat_fm_lemmas                         false
% 3.06/1.00  --sat_fm_prep                           false
% 3.06/1.00  --sat_fm_uc_incr                        true
% 3.06/1.00  --sat_out_model                         small
% 3.06/1.00  --sat_out_clauses                       false
% 3.06/1.00  
% 3.06/1.00  ------ QBF Options
% 3.06/1.00  
% 3.06/1.00  --qbf_mode                              false
% 3.06/1.00  --qbf_elim_univ                         false
% 3.06/1.00  --qbf_dom_inst                          none
% 3.06/1.00  --qbf_dom_pre_inst                      false
% 3.06/1.00  --qbf_sk_in                             false
% 3.06/1.00  --qbf_pred_elim                         true
% 3.06/1.00  --qbf_split                             512
% 3.06/1.00  
% 3.06/1.00  ------ BMC1 Options
% 3.06/1.00  
% 3.06/1.00  --bmc1_incremental                      false
% 3.06/1.00  --bmc1_axioms                           reachable_all
% 3.06/1.00  --bmc1_min_bound                        0
% 3.06/1.00  --bmc1_max_bound                        -1
% 3.06/1.00  --bmc1_max_bound_default                -1
% 3.06/1.00  --bmc1_symbol_reachability              true
% 3.06/1.00  --bmc1_property_lemmas                  false
% 3.06/1.00  --bmc1_k_induction                      false
% 3.06/1.00  --bmc1_non_equiv_states                 false
% 3.06/1.00  --bmc1_deadlock                         false
% 3.06/1.00  --bmc1_ucm                              false
% 3.06/1.00  --bmc1_add_unsat_core                   none
% 3.06/1.00  --bmc1_unsat_core_children              false
% 3.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.00  --bmc1_out_stat                         full
% 3.06/1.00  --bmc1_ground_init                      false
% 3.06/1.00  --bmc1_pre_inst_next_state              false
% 3.06/1.00  --bmc1_pre_inst_state                   false
% 3.06/1.00  --bmc1_pre_inst_reach_state             false
% 3.06/1.00  --bmc1_out_unsat_core                   false
% 3.06/1.00  --bmc1_aig_witness_out                  false
% 3.06/1.00  --bmc1_verbose                          false
% 3.06/1.00  --bmc1_dump_clauses_tptp                false
% 3.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.00  --bmc1_dump_file                        -
% 3.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.00  --bmc1_ucm_extend_mode                  1
% 3.06/1.00  --bmc1_ucm_init_mode                    2
% 3.06/1.00  --bmc1_ucm_cone_mode                    none
% 3.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.00  --bmc1_ucm_relax_model                  4
% 3.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.00  --bmc1_ucm_layered_model                none
% 3.06/1.00  --bmc1_ucm_max_lemma_size               10
% 3.06/1.00  
% 3.06/1.00  ------ AIG Options
% 3.06/1.00  
% 3.06/1.00  --aig_mode                              false
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation Options
% 3.06/1.00  
% 3.06/1.00  --instantiation_flag                    true
% 3.06/1.00  --inst_sos_flag                         false
% 3.06/1.00  --inst_sos_phase                        true
% 3.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel_side                     num_symb
% 3.06/1.00  --inst_solver_per_active                1400
% 3.06/1.00  --inst_solver_calls_frac                1.
% 3.06/1.00  --inst_passive_queue_type               priority_queues
% 3.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.00  --inst_passive_queues_freq              [25;2]
% 3.06/1.00  --inst_dismatching                      true
% 3.06/1.00  --inst_eager_unprocessed_to_passive     true
% 3.06/1.00  --inst_prop_sim_given                   true
% 3.06/1.00  --inst_prop_sim_new                     false
% 3.06/1.00  --inst_subs_new                         false
% 3.06/1.00  --inst_eq_res_simp                      false
% 3.06/1.00  --inst_subs_given                       false
% 3.06/1.00  --inst_orphan_elimination               true
% 3.06/1.00  --inst_learning_loop_flag               true
% 3.06/1.00  --inst_learning_start                   3000
% 3.06/1.00  --inst_learning_factor                  2
% 3.06/1.00  --inst_start_prop_sim_after_learn       3
% 3.06/1.00  --inst_sel_renew                        solver
% 3.06/1.00  --inst_lit_activity_flag                true
% 3.06/1.00  --inst_restr_to_given                   false
% 3.06/1.00  --inst_activity_threshold               500
% 3.06/1.00  --inst_out_proof                        true
% 3.06/1.00  
% 3.06/1.00  ------ Resolution Options
% 3.06/1.00  
% 3.06/1.00  --resolution_flag                       true
% 3.06/1.00  --res_lit_sel                           adaptive
% 3.06/1.00  --res_lit_sel_side                      none
% 3.06/1.00  --res_ordering                          kbo
% 3.06/1.00  --res_to_prop_solver                    active
% 3.06/1.00  --res_prop_simpl_new                    false
% 3.06/1.00  --res_prop_simpl_given                  true
% 3.06/1.00  --res_passive_queue_type                priority_queues
% 3.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.00  --res_passive_queues_freq               [15;5]
% 3.06/1.00  --res_forward_subs                      full
% 3.06/1.00  --res_backward_subs                     full
% 3.06/1.00  --res_forward_subs_resolution           true
% 3.06/1.00  --res_backward_subs_resolution          true
% 3.06/1.00  --res_orphan_elimination                true
% 3.06/1.00  --res_time_limit                        2.
% 3.06/1.00  --res_out_proof                         true
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Options
% 3.06/1.00  
% 3.06/1.00  --superposition_flag                    true
% 3.06/1.00  --sup_passive_queue_type                priority_queues
% 3.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.00  --demod_completeness_check              fast
% 3.06/1.00  --demod_use_ground                      true
% 3.06/1.00  --sup_to_prop_solver                    passive
% 3.06/1.00  --sup_prop_simpl_new                    true
% 3.06/1.00  --sup_prop_simpl_given                  true
% 3.06/1.00  --sup_fun_splitting                     false
% 3.06/1.00  --sup_smt_interval                      50000
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Simplification Setup
% 3.06/1.00  
% 3.06/1.00  --sup_indices_passive                   []
% 3.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_full_bw                           [BwDemod]
% 3.06/1.00  --sup_immed_triv                        [TrivRules]
% 3.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_immed_bw_main                     []
% 3.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  
% 3.06/1.00  ------ Combination Options
% 3.06/1.00  
% 3.06/1.00  --comb_res_mult                         3
% 3.06/1.00  --comb_sup_mult                         2
% 3.06/1.00  --comb_inst_mult                        10
% 3.06/1.00  
% 3.06/1.00  ------ Debug Options
% 3.06/1.00  
% 3.06/1.00  --dbg_backtrace                         false
% 3.06/1.00  --dbg_dump_prop_clauses                 false
% 3.06/1.00  --dbg_dump_prop_clauses_file            -
% 3.06/1.00  --dbg_out_stat                          false
% 3.06/1.00  ------ Parsing...
% 3.06/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.00  ------ Proving...
% 3.06/1.00  ------ Problem Properties 
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  clauses                                 31
% 3.06/1.00  conjectures                             5
% 3.06/1.00  EPR                                     4
% 3.06/1.00  Horn                                    25
% 3.06/1.00  unary                                   11
% 3.06/1.00  binary                                  6
% 3.06/1.00  lits                                    73
% 3.06/1.00  lits eq                                 26
% 3.06/1.00  fd_pure                                 0
% 3.06/1.00  fd_pseudo                               0
% 3.06/1.00  fd_cond                                 4
% 3.06/1.00  fd_pseudo_cond                          0
% 3.06/1.00  AC symbols                              0
% 3.06/1.00  
% 3.06/1.00  ------ Schedule dynamic 5 is on 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  ------ 
% 3.06/1.00  Current options:
% 3.06/1.00  ------ 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options
% 3.06/1.00  
% 3.06/1.00  --out_options                           all
% 3.06/1.00  --tptp_safe_out                         true
% 3.06/1.00  --problem_path                          ""
% 3.06/1.00  --include_path                          ""
% 3.06/1.00  --clausifier                            res/vclausify_rel
% 3.06/1.00  --clausifier_options                    --mode clausify
% 3.06/1.00  --stdin                                 false
% 3.06/1.00  --stats_out                             all
% 3.06/1.00  
% 3.06/1.00  ------ General Options
% 3.06/1.00  
% 3.06/1.00  --fof                                   false
% 3.06/1.00  --time_out_real                         305.
% 3.06/1.00  --time_out_virtual                      -1.
% 3.06/1.00  --symbol_type_check                     false
% 3.06/1.00  --clausify_out                          false
% 3.06/1.00  --sig_cnt_out                           false
% 3.06/1.00  --trig_cnt_out                          false
% 3.06/1.00  --trig_cnt_out_tolerance                1.
% 3.06/1.00  --trig_cnt_out_sk_spl                   false
% 3.06/1.00  --abstr_cl_out                          false
% 3.06/1.00  
% 3.06/1.00  ------ Global Options
% 3.06/1.00  
% 3.06/1.00  --schedule                              default
% 3.06/1.00  --add_important_lit                     false
% 3.06/1.00  --prop_solver_per_cl                    1000
% 3.06/1.00  --min_unsat_core                        false
% 3.06/1.00  --soft_assumptions                      false
% 3.06/1.00  --soft_lemma_size                       3
% 3.06/1.00  --prop_impl_unit_size                   0
% 3.06/1.00  --prop_impl_unit                        []
% 3.06/1.00  --share_sel_clauses                     true
% 3.06/1.00  --reset_solvers                         false
% 3.06/1.00  --bc_imp_inh                            [conj_cone]
% 3.06/1.00  --conj_cone_tolerance                   3.
% 3.06/1.00  --extra_neg_conj                        none
% 3.06/1.00  --large_theory_mode                     true
% 3.06/1.00  --prolific_symb_bound                   200
% 3.06/1.00  --lt_threshold                          2000
% 3.06/1.00  --clause_weak_htbl                      true
% 3.06/1.00  --gc_record_bc_elim                     false
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing Options
% 3.06/1.00  
% 3.06/1.00  --preprocessing_flag                    true
% 3.06/1.00  --time_out_prep_mult                    0.1
% 3.06/1.00  --splitting_mode                        input
% 3.06/1.00  --splitting_grd                         true
% 3.06/1.00  --splitting_cvd                         false
% 3.06/1.00  --splitting_cvd_svl                     false
% 3.06/1.00  --splitting_nvd                         32
% 3.06/1.00  --sub_typing                            true
% 3.06/1.00  --prep_gs_sim                           true
% 3.06/1.00  --prep_unflatten                        true
% 3.06/1.00  --prep_res_sim                          true
% 3.06/1.00  --prep_upred                            true
% 3.06/1.00  --prep_sem_filter                       exhaustive
% 3.06/1.00  --prep_sem_filter_out                   false
% 3.06/1.00  --pred_elim                             true
% 3.06/1.00  --res_sim_input                         true
% 3.06/1.00  --eq_ax_congr_red                       true
% 3.06/1.00  --pure_diseq_elim                       true
% 3.06/1.00  --brand_transform                       false
% 3.06/1.00  --non_eq_to_eq                          false
% 3.06/1.00  --prep_def_merge                        true
% 3.06/1.00  --prep_def_merge_prop_impl              false
% 3.06/1.00  --prep_def_merge_mbd                    true
% 3.06/1.00  --prep_def_merge_tr_red                 false
% 3.06/1.00  --prep_def_merge_tr_cl                  false
% 3.06/1.00  --smt_preprocessing                     true
% 3.06/1.00  --smt_ac_axioms                         fast
% 3.06/1.00  --preprocessed_out                      false
% 3.06/1.00  --preprocessed_stats                    false
% 3.06/1.00  
% 3.06/1.00  ------ Abstraction refinement Options
% 3.06/1.00  
% 3.06/1.00  --abstr_ref                             []
% 3.06/1.00  --abstr_ref_prep                        false
% 3.06/1.00  --abstr_ref_until_sat                   false
% 3.06/1.00  --abstr_ref_sig_restrict                funpre
% 3.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.00  --abstr_ref_under                       []
% 3.06/1.00  
% 3.06/1.00  ------ SAT Options
% 3.06/1.00  
% 3.06/1.00  --sat_mode                              false
% 3.06/1.00  --sat_fm_restart_options                ""
% 3.06/1.00  --sat_gr_def                            false
% 3.06/1.00  --sat_epr_types                         true
% 3.06/1.00  --sat_non_cyclic_types                  false
% 3.06/1.00  --sat_finite_models                     false
% 3.06/1.00  --sat_fm_lemmas                         false
% 3.06/1.00  --sat_fm_prep                           false
% 3.06/1.00  --sat_fm_uc_incr                        true
% 3.06/1.00  --sat_out_model                         small
% 3.06/1.00  --sat_out_clauses                       false
% 3.06/1.00  
% 3.06/1.00  ------ QBF Options
% 3.06/1.00  
% 3.06/1.00  --qbf_mode                              false
% 3.06/1.00  --qbf_elim_univ                         false
% 3.06/1.00  --qbf_dom_inst                          none
% 3.06/1.00  --qbf_dom_pre_inst                      false
% 3.06/1.00  --qbf_sk_in                             false
% 3.06/1.00  --qbf_pred_elim                         true
% 3.06/1.00  --qbf_split                             512
% 3.06/1.00  
% 3.06/1.00  ------ BMC1 Options
% 3.06/1.00  
% 3.06/1.00  --bmc1_incremental                      false
% 3.06/1.00  --bmc1_axioms                           reachable_all
% 3.06/1.00  --bmc1_min_bound                        0
% 3.06/1.00  --bmc1_max_bound                        -1
% 3.06/1.00  --bmc1_max_bound_default                -1
% 3.06/1.00  --bmc1_symbol_reachability              true
% 3.06/1.00  --bmc1_property_lemmas                  false
% 3.06/1.00  --bmc1_k_induction                      false
% 3.06/1.00  --bmc1_non_equiv_states                 false
% 3.06/1.00  --bmc1_deadlock                         false
% 3.06/1.00  --bmc1_ucm                              false
% 3.06/1.00  --bmc1_add_unsat_core                   none
% 3.06/1.00  --bmc1_unsat_core_children              false
% 3.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.00  --bmc1_out_stat                         full
% 3.06/1.00  --bmc1_ground_init                      false
% 3.06/1.00  --bmc1_pre_inst_next_state              false
% 3.06/1.00  --bmc1_pre_inst_state                   false
% 3.06/1.00  --bmc1_pre_inst_reach_state             false
% 3.06/1.00  --bmc1_out_unsat_core                   false
% 3.06/1.00  --bmc1_aig_witness_out                  false
% 3.06/1.00  --bmc1_verbose                          false
% 3.06/1.00  --bmc1_dump_clauses_tptp                false
% 3.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.00  --bmc1_dump_file                        -
% 3.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.00  --bmc1_ucm_extend_mode                  1
% 3.06/1.00  --bmc1_ucm_init_mode                    2
% 3.06/1.00  --bmc1_ucm_cone_mode                    none
% 3.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.00  --bmc1_ucm_relax_model                  4
% 3.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.00  --bmc1_ucm_layered_model                none
% 3.06/1.00  --bmc1_ucm_max_lemma_size               10
% 3.06/1.00  
% 3.06/1.00  ------ AIG Options
% 3.06/1.00  
% 3.06/1.00  --aig_mode                              false
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation Options
% 3.06/1.00  
% 3.06/1.00  --instantiation_flag                    true
% 3.06/1.00  --inst_sos_flag                         false
% 3.06/1.00  --inst_sos_phase                        true
% 3.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel_side                     none
% 3.06/1.00  --inst_solver_per_active                1400
% 3.06/1.00  --inst_solver_calls_frac                1.
% 3.06/1.00  --inst_passive_queue_type               priority_queues
% 3.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.00  --inst_passive_queues_freq              [25;2]
% 3.06/1.00  --inst_dismatching                      true
% 3.06/1.00  --inst_eager_unprocessed_to_passive     true
% 3.06/1.00  --inst_prop_sim_given                   true
% 3.06/1.00  --inst_prop_sim_new                     false
% 3.06/1.00  --inst_subs_new                         false
% 3.06/1.00  --inst_eq_res_simp                      false
% 3.06/1.00  --inst_subs_given                       false
% 3.06/1.00  --inst_orphan_elimination               true
% 3.06/1.00  --inst_learning_loop_flag               true
% 3.06/1.00  --inst_learning_start                   3000
% 3.06/1.00  --inst_learning_factor                  2
% 3.06/1.00  --inst_start_prop_sim_after_learn       3
% 3.06/1.00  --inst_sel_renew                        solver
% 3.06/1.00  --inst_lit_activity_flag                true
% 3.06/1.00  --inst_restr_to_given                   false
% 3.06/1.00  --inst_activity_threshold               500
% 3.06/1.00  --inst_out_proof                        true
% 3.06/1.00  
% 3.06/1.00  ------ Resolution Options
% 3.06/1.00  
% 3.06/1.00  --resolution_flag                       false
% 3.06/1.00  --res_lit_sel                           adaptive
% 3.06/1.00  --res_lit_sel_side                      none
% 3.06/1.00  --res_ordering                          kbo
% 3.06/1.00  --res_to_prop_solver                    active
% 3.06/1.00  --res_prop_simpl_new                    false
% 3.06/1.00  --res_prop_simpl_given                  true
% 3.06/1.00  --res_passive_queue_type                priority_queues
% 3.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.00  --res_passive_queues_freq               [15;5]
% 3.06/1.00  --res_forward_subs                      full
% 3.06/1.00  --res_backward_subs                     full
% 3.06/1.00  --res_forward_subs_resolution           true
% 3.06/1.00  --res_backward_subs_resolution          true
% 3.06/1.00  --res_orphan_elimination                true
% 3.06/1.00  --res_time_limit                        2.
% 3.06/1.00  --res_out_proof                         true
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Options
% 3.06/1.00  
% 3.06/1.00  --superposition_flag                    true
% 3.06/1.00  --sup_passive_queue_type                priority_queues
% 3.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.00  --demod_completeness_check              fast
% 3.06/1.00  --demod_use_ground                      true
% 3.06/1.00  --sup_to_prop_solver                    passive
% 3.06/1.00  --sup_prop_simpl_new                    true
% 3.06/1.00  --sup_prop_simpl_given                  true
% 3.06/1.00  --sup_fun_splitting                     false
% 3.06/1.00  --sup_smt_interval                      50000
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Simplification Setup
% 3.06/1.00  
% 3.06/1.00  --sup_indices_passive                   []
% 3.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_full_bw                           [BwDemod]
% 3.06/1.00  --sup_immed_triv                        [TrivRules]
% 3.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_immed_bw_main                     []
% 3.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  
% 3.06/1.00  ------ Combination Options
% 3.06/1.00  
% 3.06/1.00  --comb_res_mult                         3
% 3.06/1.00  --comb_sup_mult                         2
% 3.06/1.00  --comb_inst_mult                        10
% 3.06/1.00  
% 3.06/1.00  ------ Debug Options
% 3.06/1.00  
% 3.06/1.00  --dbg_backtrace                         false
% 3.06/1.00  --dbg_dump_prop_clauses                 false
% 3.06/1.00  --dbg_dump_prop_clauses_file            -
% 3.06/1.00  --dbg_out_stat                          false
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  ------ Proving...
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS status Theorem for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  fof(f16,conjecture,(
% 3.06/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f17,negated_conjecture,(
% 3.06/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.06/1.00    inference(negated_conjecture,[],[f16])).
% 3.06/1.00  
% 3.06/1.00  fof(f36,plain,(
% 3.06/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.06/1.00    inference(ennf_transformation,[],[f17])).
% 3.06/1.00  
% 3.06/1.00  fof(f37,plain,(
% 3.06/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.06/1.00    inference(flattening,[],[f36])).
% 3.06/1.00  
% 3.06/1.00  fof(f46,plain,(
% 3.06/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X1)) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f45,plain,(
% 3.06/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(sK3)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))) )),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f44,plain,(
% 3.06/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f47,plain,(
% 3.06/1.00    (((k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f46,f45,f44])).
% 3.06/1.00  
% 3.06/1.00  fof(f82,plain,(
% 3.06/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f11,axiom,(
% 3.06/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f28,plain,(
% 3.06/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.06/1.00    inference(ennf_transformation,[],[f11])).
% 3.06/1.00  
% 3.06/1.00  fof(f67,plain,(
% 3.06/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f28])).
% 3.06/1.00  
% 3.06/1.00  fof(f79,plain,(
% 3.06/1.00    l1_struct_0(sK3)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f77,plain,(
% 3.06/1.00    l1_struct_0(sK2)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f9,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f25,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f9])).
% 3.06/1.00  
% 3.06/1.00  fof(f60,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f25])).
% 3.06/1.00  
% 3.06/1.00  fof(f83,plain,(
% 3.06/1.00    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f10,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f26,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f10])).
% 3.06/1.00  
% 3.06/1.00  fof(f27,plain,(
% 3.06/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(flattening,[],[f26])).
% 3.06/1.00  
% 3.06/1.00  fof(f39,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(nnf_transformation,[],[f27])).
% 3.06/1.00  
% 3.06/1.00  fof(f61,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f39])).
% 3.06/1.00  
% 3.06/1.00  fof(f8,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f24,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f8])).
% 3.06/1.00  
% 3.06/1.00  fof(f59,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f24])).
% 3.06/1.00  
% 3.06/1.00  fof(f81,plain,(
% 3.06/1.00    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f14,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f32,plain,(
% 3.06/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.06/1.00    inference(ennf_transformation,[],[f14])).
% 3.06/1.00  
% 3.06/1.00  fof(f33,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.06/1.00    inference(flattening,[],[f32])).
% 3.06/1.00  
% 3.06/1.00  fof(f73,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f33])).
% 3.06/1.00  
% 3.06/1.00  fof(f84,plain,(
% 3.06/1.00    v2_funct_1(sK4)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f80,plain,(
% 3.06/1.00    v1_funct_1(sK4)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f15,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f34,plain,(
% 3.06/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.06/1.00    inference(ennf_transformation,[],[f15])).
% 3.06/1.00  
% 3.06/1.00  fof(f35,plain,(
% 3.06/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.06/1.00    inference(flattening,[],[f34])).
% 3.06/1.00  
% 3.06/1.00  fof(f76,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f35])).
% 3.06/1.00  
% 3.06/1.00  fof(f7,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f23,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f7])).
% 3.06/1.00  
% 3.06/1.00  fof(f58,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f23])).
% 3.06/1.00  
% 3.06/1.00  fof(f6,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f21,plain,(
% 3.06/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f6])).
% 3.06/1.00  
% 3.06/1.00  fof(f22,plain,(
% 3.06/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f21])).
% 3.06/1.00  
% 3.06/1.00  fof(f57,plain,(
% 3.06/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f22])).
% 3.06/1.00  
% 3.06/1.00  fof(f85,plain,(
% 3.06/1.00    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f56,plain,(
% 3.06/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f22])).
% 3.06/1.00  
% 3.06/1.00  fof(f12,axiom,(
% 3.06/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f19,plain,(
% 3.06/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.06/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.06/1.00  
% 3.06/1.00  fof(f29,plain,(
% 3.06/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f19])).
% 3.06/1.00  
% 3.06/1.00  fof(f30,plain,(
% 3.06/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.06/1.00    inference(flattening,[],[f29])).
% 3.06/1.00  
% 3.06/1.00  fof(f40,plain,(
% 3.06/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f41,plain,(
% 3.06/1.00    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f40])).
% 3.06/1.00  
% 3.06/1.00  fof(f68,plain,(
% 3.06/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f41])).
% 3.06/1.00  
% 3.06/1.00  fof(f78,plain,(
% 3.06/1.00    ~v2_struct_0(sK3)),
% 3.06/1.00    inference(cnf_transformation,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f2,axiom,(
% 3.06/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f20,plain,(
% 3.06/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f2])).
% 3.06/1.00  
% 3.06/1.00  fof(f38,plain,(
% 3.06/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.06/1.00    inference(nnf_transformation,[],[f20])).
% 3.06/1.00  
% 3.06/1.00  fof(f49,plain,(
% 3.06/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f38])).
% 3.06/1.00  
% 3.06/1.00  fof(f13,axiom,(
% 3.06/1.00    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k3_tarski(X0) != k1_xboole_0) & ~(k3_tarski(X0) = k1_xboole_0 & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f18,plain,(
% 3.06/1.00    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k3_tarski(X0) != k1_xboole_0) & ~(k3_tarski(X0) = k1_xboole_0 & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 3.06/1.00    inference(rectify,[],[f13])).
% 3.06/1.00  
% 3.06/1.00  fof(f31,plain,(
% 3.06/1.00    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k3_tarski(X0) = k1_xboole_0) & (k3_tarski(X0) != k1_xboole_0 | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.06/1.00    inference(ennf_transformation,[],[f18])).
% 3.06/1.00  
% 3.06/1.00  fof(f42,plain,(
% 3.06/1.00    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f43,plain,(
% 3.06/1.00    ! [X0] : (((r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)) | k3_tarski(X0) = k1_xboole_0) & (k3_tarski(X0) != k1_xboole_0 | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f42])).
% 3.06/1.00  
% 3.06/1.00  fof(f70,plain,(
% 3.06/1.00    ( ! [X2,X0] : (k3_tarski(X0) != k1_xboole_0 | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 3.06/1.00    inference(cnf_transformation,[],[f43])).
% 3.06/1.00  
% 3.06/1.00  fof(f69,plain,(
% 3.06/1.00    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f41])).
% 3.06/1.00  
% 3.06/1.00  fof(f1,axiom,(
% 3.06/1.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f48,plain,(
% 3.06/1.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.06/1.00    inference(cnf_transformation,[],[f1])).
% 3.06/1.00  
% 3.06/1.00  fof(f4,axiom,(
% 3.06/1.00    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f54,plain,(
% 3.06/1.00    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f4])).
% 3.06/1.00  
% 3.06/1.00  fof(f3,axiom,(
% 3.06/1.00    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f53,plain,(
% 3.06/1.00    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 3.06/1.00    inference(cnf_transformation,[],[f3])).
% 3.06/1.00  
% 3.06/1.00  fof(f86,plain,(
% 3.06/1.00    v1_xboole_0(k1_xboole_0)),
% 3.06/1.00    inference(definition_unfolding,[],[f54,f53])).
% 3.06/1.00  
% 3.06/1.00  fof(f5,axiom,(
% 3.06/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f55,plain,(
% 3.06/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f5])).
% 3.06/1.00  
% 3.06/1.00  cnf(c_31,negated_conjecture,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1215,plain,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_18,plain,
% 3.06/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_34,negated_conjecture,
% 3.06/1.00      ( l1_struct_0(sK3) ),
% 3.06/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_399,plain,
% 3.06/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_400,plain,
% 3.06/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_399]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_36,negated_conjecture,
% 3.06/1.00      ( l1_struct_0(sK2) ),
% 3.06/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_404,plain,
% 3.06/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_405,plain,
% 3.06/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_404]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1254,plain,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) = iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_1215,c_400,c_405]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_11,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1225,plain,
% 3.06/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1907,plain,
% 3.06/1.00      ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1254,c_1225]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_30,negated_conjecture,
% 3.06/1.00      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 3.06/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1251,plain,
% 3.06/1.00      ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_30,c_400,c_405]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2036,plain,
% 3.06/1.00      ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_1907,c_1251]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2433,plain,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) = iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_2036,c_1254]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_17,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1219,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.06/1.00      | k1_xboole_0 = X1
% 3.06/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3378,plain,
% 3.06/1.00      ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_struct_0(sK2)
% 3.06/1.00      | k2_relat_1(sK4) = k1_xboole_0
% 3.06/1.00      | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2433,c_1219]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_10,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1226,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2184,plain,
% 3.06/1.00      ( k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1254,c_1226]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2720,plain,
% 3.06/1.00      ( k1_relset_1(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_2184,c_2036]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3382,plain,
% 3.06/1.00      ( k2_struct_0(sK2) = k1_relat_1(sK4)
% 3.06/1.00      | k2_relat_1(sK4) = k1_xboole_0
% 3.06/1.00      | v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_3378,c_2720]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_32,negated_conjecture,
% 3.06/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1214,plain,
% 3.06/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1248,plain,
% 3.06/1.00      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_1214,c_400,c_405]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2434,plain,
% 3.06/1.00      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) = iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_2036,c_1248]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3668,plain,
% 3.06/1.00      ( k2_relat_1(sK4) = k1_xboole_0
% 3.06/1.00      | k2_struct_0(sK2) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_3382,c_2434]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3669,plain,
% 3.06/1.00      ( k2_struct_0(sK2) = k1_relat_1(sK4)
% 3.06/1.00      | k2_relat_1(sK4) = k1_xboole_0 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_3668]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_24,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v2_funct_1(X0)
% 3.06/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.06/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.06/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_29,negated_conjecture,
% 3.06/1.00      ( v2_funct_1(sK4) ),
% 3.06/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_453,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.06/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_454,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.06/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | ~ v1_funct_1(sK4)
% 3.06/1.00      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.06/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_33,negated_conjecture,
% 3.06/1.00      ( v1_funct_1(sK4) ),
% 3.06/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_458,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | ~ v1_funct_2(sK4,X0,X1)
% 3.06/1.00      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.06/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_454,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_459,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.06/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.06/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_458]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1210,plain,
% 3.06/1.00      ( k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.06/1.00      | k2_relset_1(X0,X1,sK4) != X1
% 3.06/1.00      | v1_funct_2(sK4,X0,X1) != iProver_top
% 3.06/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1781,plain,
% 3.06/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
% 3.06/1.00      | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.06/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1251,c_1210]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1784,plain,
% 3.06/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_1781,c_1254,c_1248]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2432,plain,
% 3.06/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_relat_1(sK4),sK4) = k2_funct_1(sK4) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_2036,c_1784]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_25,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1218,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.06/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/1.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 3.06/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4037,plain,
% 3.06/1.00      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_relat_1(sK4)) != iProver_top
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top
% 3.06/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_relat_1(sK4)))) != iProver_top
% 3.06/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2432,c_1218]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_40,plain,
% 3.06/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4368,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k2_struct_0(sK2)))) = iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4037,c_40,c_2433,c_2434]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4377,plain,
% 3.06/1.00      ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4368,c_1225]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7,plain,
% 3.06/1.00      ( ~ v1_relat_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v2_funct_1(X0)
% 3.06/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_491,plain,
% 3.06/1.00      ( ~ v1_relat_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_492,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK4)
% 3.06/1.00      | ~ v1_funct_1(sK4)
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_491]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_494,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK4)
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_492,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_516,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_494]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_517,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1209,plain,
% 3.06/1.00      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.06/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1442,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_517]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1900,plain,
% 3.06/1.00      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_1209,c_31,c_1442]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4386,plain,
% 3.06/1.00      ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_4377,c_1900]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_28,negated_conjecture,
% 3.06/1.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 3.06/1.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
% 3.06/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1345,plain,
% 3.06/1.00      ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 3.06/1.00      | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_28,c_400,c_405]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1787,plain,
% 3.06/1.00      ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
% 3.06/1.00      | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_1784,c_1345]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2431,plain,
% 3.06/1.00      ( k2_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
% 3.06/1.00      | k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_2036,c_1787]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4447,plain,
% 3.06/1.00      ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_relat_1(sK4)
% 3.06/1.00      | k2_struct_0(sK2) != k1_relat_1(sK4) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_4386,c_2431]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4376,plain,
% 3.06/1.00      ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4368,c_1226]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8,plain,
% 3.06/1.00      ( ~ v1_relat_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v2_funct_1(X0)
% 3.06/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_477,plain,
% 3.06/1.00      ( ~ v1_relat_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_478,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK4)
% 3.06/1.00      | ~ v1_funct_1(sK4)
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_480,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK4)
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_478,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_528,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_480]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_529,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_528]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1208,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.06/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1445,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_529]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1858,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_1208,c_31,c_1445]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4389,plain,
% 3.06/1.00      ( k1_relset_1(k2_relat_1(sK4),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_4376,c_1858]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4563,plain,
% 3.06/1.00      ( k2_struct_0(sK2) != k1_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4447,c_4389]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4566,plain,
% 3.06/1.00      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_3669,c_4563]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_20,plain,
% 3.06/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.06/1.00      | v2_struct_0(X0)
% 3.06/1.00      | ~ l1_struct_0(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_35,negated_conjecture,
% 3.06/1.00      ( ~ v2_struct_0(sK3) ),
% 3.06/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_373,plain,
% 3.06/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.06/1.00      | ~ l1_struct_0(X0)
% 3.06/1.00      | sK3 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_374,plain,
% 3.06/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.06/1.00      | ~ l1_struct_0(sK3) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_373]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_376,plain,
% 3.06/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_374,c_34]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1212,plain,
% 3.06/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1245,plain,
% 3.06/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_1212,c_400]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2435,plain,
% 3.06/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_relat_1(sK4))) = iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_2036,c_1245]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4581,plain,
% 3.06/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_4566,c_2435]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4,plain,
% 3.06/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_23,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,X1)
% 3.06/1.00      | k3_tarski(X1) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0 ),
% 3.06/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_546,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,X1)
% 3.06/1.00      | v1_xboole_0(X1)
% 3.06/1.00      | k3_tarski(X1) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0 ),
% 3.06/1.00      inference(resolution,[status(thm)],[c_4,c_23]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1490,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/1.00      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.06/1.00      | k3_tarski(k1_zfmisc_1(X1)) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_546]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2592,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(X0))
% 3.06/1.00      | v1_xboole_0(k1_zfmisc_1(X0))
% 3.06/1.00      | k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = sK0(sK3) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1490]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2599,plain,
% 3.06/1.00      ( k3_tarski(k1_zfmisc_1(X0)) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = sK0(sK3)
% 3.06/1.00      | m1_subset_1(sK0(sK3),k1_zfmisc_1(X0)) != iProver_top
% 3.06/1.00      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2592]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2601,plain,
% 3.06/1.00      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = sK0(sK3)
% 3.06/1.00      | m1_subset_1(sK0(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.06/1.00      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2599]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_761,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1624,plain,
% 3.06/1.00      ( X0 != X1 | sK0(sK3) != X1 | sK0(sK3) = X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_761]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1884,plain,
% 3.06/1.00      ( X0 != sK0(sK3) | sK0(sK3) = X0 | sK0(sK3) != sK0(sK3) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1624]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1886,plain,
% 3.06/1.00      ( sK0(sK3) != sK0(sK3)
% 3.06/1.00      | sK0(sK3) = k1_xboole_0
% 3.06/1.00      | k1_xboole_0 != sK0(sK3) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1884]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_760,plain,( X0 = X0 ),theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1882,plain,
% 3.06/1.00      ( sK3 = sK3 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_760]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_776,plain,( X0 != X1 | sK0(X0) = sK0(X1) ),theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1626,plain,
% 3.06/1.00      ( sK0(sK3) = sK0(X0) | sK3 != X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_776]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1881,plain,
% 3.06/1.00      ( sK0(sK3) = sK0(sK3) | sK3 != sK3 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1626]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_765,plain,
% 3.06/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.06/1.00      theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1476,plain,
% 3.06/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0(sK3)) | sK0(sK3) != X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_765]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1478,plain,
% 3.06/1.00      ( v1_xboole_0(sK0(sK3))
% 3.06/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.06/1.00      | sK0(sK3) != k1_xboole_0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1476]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_19,plain,
% 3.06/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(sK0(X0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_384,plain,
% 3.06/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(sK0(X0)) | sK3 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_385,plain,
% 3.06/1.00      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(sK0(sK3)) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_384]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_0,plain,
% 3.06/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.06/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_115,plain,
% 3.06/1.00      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5,plain,
% 3.06/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6,plain,
% 3.06/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_105,plain,
% 3.06/1.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_107,plain,
% 3.06/1.00      ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_105]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(contradiction,plain,
% 3.06/1.00      ( $false ),
% 3.06/1.00      inference(minisat,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4581,c_2601,c_1886,c_1882,c_1881,c_1478,c_385,c_115,
% 3.06/1.00                 c_5,c_107,c_34]) ).
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  ------                               Statistics
% 3.06/1.00  
% 3.06/1.00  ------ General
% 3.06/1.00  
% 3.06/1.00  abstr_ref_over_cycles:                  0
% 3.06/1.00  abstr_ref_under_cycles:                 0
% 3.06/1.00  gc_basic_clause_elim:                   0
% 3.06/1.00  forced_gc_time:                         0
% 3.06/1.00  parsing_time:                           0.015
% 3.06/1.00  unif_index_cands_time:                  0.
% 3.06/1.00  unif_index_add_time:                    0.
% 3.06/1.00  orderings_time:                         0.
% 3.06/1.00  out_proof_time:                         0.012
% 3.06/1.00  total_time:                             0.166
% 3.06/1.00  num_of_symbols:                         57
% 3.06/1.00  num_of_terms:                           3941
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing
% 3.06/1.00  
% 3.06/1.00  num_of_splits:                          0
% 3.06/1.00  num_of_split_atoms:                     0
% 3.06/1.00  num_of_reused_defs:                     0
% 3.06/1.00  num_eq_ax_congr_red:                    7
% 3.06/1.00  num_of_sem_filtered_clauses:            1
% 3.06/1.00  num_of_subtypes:                        0
% 3.06/1.00  monotx_restored_types:                  0
% 3.06/1.00  sat_num_of_epr_types:                   0
% 3.06/1.00  sat_num_of_non_cyclic_types:            0
% 3.06/1.00  sat_guarded_non_collapsed_types:        0
% 3.06/1.00  num_pure_diseq_elim:                    0
% 3.06/1.00  simp_replaced_by:                       0
% 3.06/1.00  res_preprocessed:                       167
% 3.06/1.00  prep_upred:                             0
% 3.06/1.00  prep_unflattend:                        13
% 3.06/1.00  smt_new_axioms:                         0
% 3.06/1.00  pred_elim_cands:                        4
% 3.06/1.00  pred_elim:                              5
% 3.06/1.00  pred_elim_cl:                           6
% 3.06/1.00  pred_elim_cycles:                       8
% 3.06/1.00  merged_defs:                            0
% 3.06/1.00  merged_defs_ncl:                        0
% 3.06/1.00  bin_hyper_res:                          0
% 3.06/1.00  prep_cycles:                            4
% 3.06/1.00  pred_elim_time:                         0.004
% 3.06/1.00  splitting_time:                         0.
% 3.06/1.00  sem_filter_time:                        0.
% 3.06/1.00  monotx_time:                            0.
% 3.06/1.00  subtype_inf_time:                       0.
% 3.06/1.00  
% 3.06/1.00  ------ Problem properties
% 3.06/1.00  
% 3.06/1.00  clauses:                                31
% 3.06/1.00  conjectures:                            5
% 3.06/1.00  epr:                                    4
% 3.06/1.00  horn:                                   25
% 3.06/1.00  ground:                                 10
% 3.06/1.00  unary:                                  11
% 3.06/1.00  binary:                                 6
% 3.06/1.00  lits:                                   73
% 3.06/1.00  lits_eq:                                26
% 3.06/1.00  fd_pure:                                0
% 3.06/1.00  fd_pseudo:                              0
% 3.06/1.00  fd_cond:                                4
% 3.06/1.00  fd_pseudo_cond:                         0
% 3.06/1.00  ac_symbols:                             0
% 3.06/1.00  
% 3.06/1.00  ------ Propositional Solver
% 3.06/1.00  
% 3.06/1.00  prop_solver_calls:                      28
% 3.06/1.00  prop_fast_solver_calls:                 1020
% 3.06/1.00  smt_solver_calls:                       0
% 3.06/1.00  smt_fast_solver_calls:                  0
% 3.06/1.00  prop_num_of_clauses:                    1537
% 3.06/1.00  prop_preprocess_simplified:             5723
% 3.06/1.00  prop_fo_subsumed:                       23
% 3.06/1.00  prop_solver_time:                       0.
% 3.06/1.00  smt_solver_time:                        0.
% 3.06/1.00  smt_fast_solver_time:                   0.
% 3.06/1.00  prop_fast_solver_time:                  0.
% 3.06/1.00  prop_unsat_core_time:                   0.
% 3.06/1.00  
% 3.06/1.00  ------ QBF
% 3.06/1.00  
% 3.06/1.00  qbf_q_res:                              0
% 3.06/1.00  qbf_num_tautologies:                    0
% 3.06/1.00  qbf_prep_cycles:                        0
% 3.06/1.00  
% 3.06/1.00  ------ BMC1
% 3.06/1.00  
% 3.06/1.00  bmc1_current_bound:                     -1
% 3.06/1.00  bmc1_last_solved_bound:                 -1
% 3.06/1.00  bmc1_unsat_core_size:                   -1
% 3.06/1.00  bmc1_unsat_core_parents_size:           -1
% 3.06/1.00  bmc1_merge_next_fun:                    0
% 3.06/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation
% 3.06/1.00  
% 3.06/1.00  inst_num_of_clauses:                    519
% 3.06/1.00  inst_num_in_passive:                    175
% 3.06/1.00  inst_num_in_active:                     254
% 3.06/1.00  inst_num_in_unprocessed:                90
% 3.06/1.00  inst_num_of_loops:                      280
% 3.06/1.00  inst_num_of_learning_restarts:          0
% 3.06/1.00  inst_num_moves_active_passive:          23
% 3.06/1.00  inst_lit_activity:                      0
% 3.06/1.00  inst_lit_activity_moves:                0
% 3.06/1.00  inst_num_tautologies:                   0
% 3.06/1.00  inst_num_prop_implied:                  0
% 3.06/1.00  inst_num_existing_simplified:           0
% 3.06/1.00  inst_num_eq_res_simplified:             0
% 3.06/1.00  inst_num_child_elim:                    0
% 3.06/1.00  inst_num_of_dismatching_blockings:      143
% 3.06/1.00  inst_num_of_non_proper_insts:           452
% 3.06/1.00  inst_num_of_duplicates:                 0
% 3.06/1.00  inst_inst_num_from_inst_to_res:         0
% 3.06/1.00  inst_dismatching_checking_time:         0.
% 3.06/1.00  
% 3.06/1.00  ------ Resolution
% 3.06/1.00  
% 3.06/1.00  res_num_of_clauses:                     0
% 3.06/1.00  res_num_in_passive:                     0
% 3.06/1.00  res_num_in_active:                      0
% 3.06/1.00  res_num_of_loops:                       171
% 3.06/1.00  res_forward_subset_subsumed:            52
% 3.06/1.00  res_backward_subset_subsumed:           4
% 3.06/1.00  res_forward_subsumed:                   0
% 3.06/1.00  res_backward_subsumed:                  0
% 3.06/1.00  res_forward_subsumption_resolution:     0
% 3.06/1.00  res_backward_subsumption_resolution:    0
% 3.06/1.00  res_clause_to_clause_subsumption:       131
% 3.06/1.00  res_orphan_elimination:                 0
% 3.06/1.00  res_tautology_del:                      26
% 3.06/1.00  res_num_eq_res_simplified:              0
% 3.06/1.00  res_num_sel_changes:                    0
% 3.06/1.00  res_moves_from_active_to_pass:          0
% 3.06/1.00  
% 3.06/1.00  ------ Superposition
% 3.06/1.00  
% 3.06/1.00  sup_time_total:                         0.
% 3.06/1.00  sup_time_generating:                    0.
% 3.06/1.00  sup_time_sim_full:                      0.
% 3.06/1.00  sup_time_sim_immed:                     0.
% 3.06/1.00  
% 3.06/1.00  sup_num_of_clauses:                     56
% 3.06/1.00  sup_num_in_active:                      29
% 3.06/1.00  sup_num_in_passive:                     27
% 3.06/1.00  sup_num_of_loops:                       55
% 3.06/1.00  sup_fw_superposition:                   27
% 3.06/1.00  sup_bw_superposition:                   34
% 3.06/1.00  sup_immediate_simplified:               30
% 3.06/1.00  sup_given_eliminated:                   0
% 3.06/1.00  comparisons_done:                       0
% 3.06/1.00  comparisons_avoided:                    12
% 3.06/1.00  
% 3.06/1.00  ------ Simplifications
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  sim_fw_subset_subsumed:                 6
% 3.06/1.00  sim_bw_subset_subsumed:                 5
% 3.06/1.00  sim_fw_subsumed:                        13
% 3.06/1.00  sim_bw_subsumed:                        0
% 3.06/1.00  sim_fw_subsumption_res:                 3
% 3.06/1.00  sim_bw_subsumption_res:                 0
% 3.06/1.00  sim_tautology_del:                      2
% 3.06/1.00  sim_eq_tautology_del:                   1
% 3.06/1.00  sim_eq_res_simp:                        0
% 3.06/1.00  sim_fw_demodulated:                     6
% 3.06/1.00  sim_bw_demodulated:                     25
% 3.06/1.00  sim_light_normalised:                   11
% 3.06/1.00  sim_joinable_taut:                      0
% 3.06/1.00  sim_joinable_simp:                      0
% 3.06/1.00  sim_ac_normalised:                      0
% 3.06/1.00  sim_smt_subsumption:                    0
% 3.06/1.00  
%------------------------------------------------------------------------------
