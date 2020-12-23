%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  157 (5015 expanded)
%              Number of leaves         :   18 (1818 expanded)
%              Depth                    :   64
%              Number of atoms          :  660 (40174 expanded)
%              Number of equality atoms :  250 (14477 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(resolution,[],[f413,f329])).

fof(f329,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f92,f325])).

fof(f325,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f315,f92])).

fof(f315,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k2_struct_0(sK1) ) ),
    inference(resolution,[],[f306,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f306,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f305,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

fof(f305,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f303,f51])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f303,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f302])).

fof(f302,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f298,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f298,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_struct_0(sK1))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(superposition,[],[f294,f163])).

fof(f163,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f162,f92])).

fof(f162,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f161,f90])).

fof(f90,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f88,f84])).

fof(f84,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f88,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f50,f83])).

fof(f83,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f161,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f152,f93])).

fof(f93,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f85,f84])).

fof(f85,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f48,f83])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X1,X0)
      | k6_relat_1(X0) = k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X1,X0,sK2) != X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f151,f47])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_relat_1(X0) = k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X1,X0,sK2) != X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK2,X1,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f74,f54])).

fof(f54,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f294,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f293,f47])).

fof(f293,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f292,f93])).

fof(f292,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f291,f92])).

fof(f291,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f290,f51])).

fof(f290,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f288,f90])).

fof(f288,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f287,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f287,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f286,f92])).

fof(f286,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f285,f90])).

fof(f285,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(resolution,[],[f278,f93])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) ) ),
    inference(subsumption_resolution,[],[f277,f92])).

fof(f277,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f276,f90])).

fof(f276,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f264,f93])).

fof(f264,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_relset_1(X2,X3,sK2) != X3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK2,X2,X3) ) ),
    inference(subsumption_resolution,[],[f263,f92])).

fof(f263,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_relset_1(X2,X3,sK2) != X3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK2,X2,X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ) ),
    inference(superposition,[],[f244,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f244,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_relset_1(X2,X3,sK2) != X3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK2,X2,X3) ) ),
    inference(subsumption_resolution,[],[f243,f47])).

fof(f243,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X2,X3,sK2) != X3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK2,X2,X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f242,f51])).

fof(f242,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X2,X3,sK2) != X3
      | ~ v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK2,X2,X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f228,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f227,f47])).

fof(f227,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f226,f92])).

fof(f226,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f190,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f190,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f189,f47])).

fof(f189,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f188,f51])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f179,f69])).

fof(f179,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f178,f47])).

fof(f178,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f177,f92])).

fof(f177,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f139,f76])).

fof(f139,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f138,plain,
    ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f93])).

fof(f137,plain,
    ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f92])).

fof(f136,plain,
    ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f90])).

fof(f135,plain,
    ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,
    ( k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f94,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) ),
    inference(forward_demodulation,[],[f91,f84])).

fof(f91,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(u1_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) ),
    inference(backward_demodulation,[],[f89,f84])).

fof(f89,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(u1_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK2)
    | k1_partfun1(k2_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f87,f83])).

fof(f87,plain,
    ( k1_partfun1(k2_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f82,f83])).

fof(f82,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f77,f50])).

fof(f77,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(definition_unfolding,[],[f52,f54,f54])).

fof(f52,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f86,f84])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f49,f83])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f413,plain,(
    ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(subsumption_resolution,[],[f412,f65])).

fof(f412,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f411,f47])).

fof(f411,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f410,f51])).

fof(f410,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f409])).

fof(f409,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f404,f56])).

fof(f404,plain,(
    ! [X0,X1] :
      ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f383,f65])).

fof(f383,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f382])).

fof(f382,plain,
    ( k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0)
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f349,f362])).

fof(f362,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f361,f325])).

fof(f361,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f339,f160])).

fof(f160,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f158,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f155,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f155,plain,(
    ! [X0] :
      ( ~ v5_relat_1(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f153,f65])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f58,f143])).

fof(f143,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f126,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f126,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k2_relat_1(k1_xboole_0))
      | k2_relat_1(k1_xboole_0) = X5 ) ),
    inference(subsumption_resolution,[],[f123,f53])).

fof(f123,plain,(
    ! [X6,X5] :
      ( k2_relat_1(k1_xboole_0) = X5
      | ~ r1_tarski(X5,k2_relat_1(k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) ) ),
    inference(resolution,[],[f118,f53])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(X1) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X0))) ) ),
    inference(resolution,[],[f109,f68])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k2_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f97,f65])).

fof(f97,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X4)
      | ~ r1_tarski(X3,k2_relat_1(X4))
      | ~ v5_relat_1(X4,X3)
      | k2_relat_1(X4) = X3 ) ),
    inference(resolution,[],[f62,f58])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f339,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f186,f325])).

fof(f186,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_relat_1(sK2))
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(resolution,[],[f125,f92])).

fof(f125,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
      | ~ r1_tarski(X12,k2_relat_1(sK2))
      | k2_relat_1(sK2) = X12 ) ),
    inference(resolution,[],[f118,f92])).

fof(f349,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_xboole_0)
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f300,f325])).

fof(f300,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f299,f47])).

fof(f299,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f297,f51])).

fof(f297,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f294,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (2215)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (2207)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (2199)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (2201)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (2207)Refutation not found, incomplete strategy% (2207)------------------------------
% 0.20/0.51  % (2207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (2207)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (2207)Memory used [KB]: 1791
% 0.20/0.51  % (2207)Time elapsed: 0.055 s
% 0.20/0.51  % (2207)------------------------------
% 0.20/0.51  % (2207)------------------------------
% 0.20/0.51  % (2196)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (2197)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (2198)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (2217)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (2205)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (2195)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (2209)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (2219)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (2193)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (2206)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (2209)Refutation not found, incomplete strategy% (2209)------------------------------
% 0.20/0.52  % (2209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2209)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2209)Memory used [KB]: 10618
% 0.20/0.52  % (2209)Time elapsed: 0.105 s
% 0.20/0.52  % (2209)------------------------------
% 0.20/0.52  % (2209)------------------------------
% 0.20/0.52  % (2194)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (2221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (2211)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (2194)Refutation not found, incomplete strategy% (2194)------------------------------
% 0.20/0.53  % (2194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2194)Memory used [KB]: 1791
% 0.20/0.53  % (2194)Time elapsed: 0.121 s
% 0.20/0.53  % (2194)------------------------------
% 0.20/0.53  % (2194)------------------------------
% 0.20/0.53  % (2212)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (2210)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (2200)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (2222)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (2203)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (2204)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (2214)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (2218)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (2215)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f416,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(resolution,[],[f413,f329])).
% 0.20/0.54  fof(f329,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 0.20/0.54    inference(backward_demodulation,[],[f92,f325])).
% 0.20/0.54  fof(f325,plain,(
% 0.20/0.54    k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f315,f92])).
% 0.20/0.54  fof(f315,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k2_struct_0(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f306,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f306,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f305,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    (((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f39,f38,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).
% 0.20/0.54  fof(f305,plain,(
% 0.20/0.54    k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f303,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    v2_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f302])).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(superposition,[],[f298,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f296])).
% 0.20/0.54  fof(f296,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_struct_0(sK1)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(superposition,[],[f294,f163])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f162,f92])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f161,f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f88,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f55,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    l1_struct_0(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f50,f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f55,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    l1_struct_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f152,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f85,f84])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f48,f83])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,X1,X0) | k6_relat_1(X0) = k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f151,f47])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_relat_1(X0) = k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(resolution,[],[f78,f51])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f74,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.54  fof(f294,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f293,f47])).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f292,f93])).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f291,f92])).
% 0.20/0.54  fof(f291,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f290,f51])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f288,f90])).
% 0.20/0.54  fof(f288,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f287,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f286,f92])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f285,f90])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.20/0.54    inference(resolution,[],[f278,f93])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f277,f92])).
% 0.20/0.54  fof(f277,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f276,f90])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f264,f93])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X0,X1) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_relset_1(X2,X3,sK2) != X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f263,f92])).
% 0.20/0.54  fof(f263,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_relset_1(X2,X3,sK2) != X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))) )),
% 0.20/0.54    inference(superposition,[],[f244,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f244,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_relset_1(X2,X3,sK2) != X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f243,f47])).
% 0.20/0.54  fof(f243,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X2,X3,sK2) != X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f242,f51])).
% 0.20/0.54  fof(f242,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X2,X3,sK2) != X3 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(resolution,[],[f228,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f228,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f227,f47])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f226,f92])).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f225])).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(superposition,[],[f190,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.54    inference(flattening,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f189,f47])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f188,f51])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.20/0.54    inference(resolution,[],[f179,f69])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    ~v1_funct_1(k2_funct_1(sK2)) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f178,f47])).
% 0.20/0.54  fof(f178,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f177,f92])).
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.54    inference(superposition,[],[f139,f76])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f138,f47])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f137,f93])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f136,f92])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f135,f90])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f133,f51])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.54    inference(superposition,[],[f94,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f91,f84])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(u1_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f89,f84])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(u1_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) | k1_partfun1(k2_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.54    inference(forward_demodulation,[],[f87,f83])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    k1_partfun1(k2_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f82,f83])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.54    inference(backward_demodulation,[],[f77,f50])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.54    inference(definition_unfolding,[],[f52,f54,f54])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.54    inference(backward_demodulation,[],[f86,f84])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.54    inference(backward_demodulation,[],[f49,f83])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f413,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f412,f65])).
% 0.20/0.54  fof(f412,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f411,f47])).
% 0.20/0.54  fof(f411,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f410,f51])).
% 0.20/0.54  fof(f410,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f409])).
% 0.20/0.54  fof(f409,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.54    inference(superposition,[],[f404,f56])).
% 0.20/0.54  fof(f404,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(resolution,[],[f383,f65])).
% 0.20/0.54  fof(f383,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f382])).
% 0.20/0.54  fof(f382,plain,(
% 0.20/0.54    k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f349,f362])).
% 0.20/0.54  fof(f362,plain,(
% 0.20/0.54    k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.54    inference(forward_demodulation,[],[f361,f325])).
% 0.20/0.54  fof(f361,plain,(
% 0.20/0.54    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f339,f160])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f158,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.54    inference(resolution,[],[f155,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X0] : (~v5_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f154,f53])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v5_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.54    inference(resolution,[],[f153,f65])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(superposition,[],[f58,f143])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.54    inference(resolution,[],[f128,f53])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(k1_xboole_0))) | k2_relat_1(k1_xboole_0) = X0) )),
% 0.20/0.54    inference(resolution,[],[f126,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ( ! [X5] : (~r1_tarski(X5,k2_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f123,f53])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k2_relat_1(k1_xboole_0) = X5 | ~r1_tarski(X5,k2_relat_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))) )),
% 0.20/0.54    inference(resolution,[],[f118,f53])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(X1) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X0)))) )),
% 0.20/0.54    inference(resolution,[],[f109,f68])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~v5_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k2_relat_1(X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.20/0.54    inference(resolution,[],[f97,f65])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X4,X3] : (~v1_relat_1(X4) | ~r1_tarski(X3,k2_relat_1(X4)) | ~v5_relat_1(X4,X3) | k2_relat_1(X4) = X3) )),
% 0.20/0.54    inference(resolution,[],[f62,f58])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.54  fof(f339,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f186,f325])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    ~r1_tarski(k2_struct_0(sK1),k2_relat_1(sK2)) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.54    inference(resolution,[],[f125,f92])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ( ! [X12,X13] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X13,X12))) | ~r1_tarski(X12,k2_relat_1(sK2)) | k2_relat_1(sK2) = X12) )),
% 0.20/0.54    inference(resolution,[],[f118,f92])).
% 0.20/0.54  fof(f349,plain,(
% 0.20/0.54    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_xboole_0) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f300,f325])).
% 0.20/0.54  fof(f300,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f299,f47])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f297,f51])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.54    inference(superposition,[],[f294,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (2215)------------------------------
% 0.20/0.54  % (2215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2215)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (2215)Memory used [KB]: 6652
% 0.20/0.54  % (2215)Time elapsed: 0.072 s
% 0.20/0.54  % (2215)------------------------------
% 0.20/0.54  % (2215)------------------------------
% 0.20/0.54  % (2192)Success in time 0.175 s
%------------------------------------------------------------------------------
