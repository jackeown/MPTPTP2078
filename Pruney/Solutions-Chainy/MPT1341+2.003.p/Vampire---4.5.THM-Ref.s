%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 (4015 expanded)
%              Number of leaves         :   14 (1453 expanded)
%              Depth                    :   25
%              Number of atoms          :  341 (30718 expanded)
%              Number of equality atoms :  123 (11111 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f165])).

fof(f165,plain,(
    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK3))
    | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f119,f163])).

fof(f163,plain,(
    k6_relat_1(k2_relat_1(sK3)) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) ),
    inference(forward_demodulation,[],[f162,f91])).

fof(f91,plain,(
    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f90,f68])).

fof(f68,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f59,f57])).

fof(f57,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
      | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
    & v2_funct_1(sK3)
    & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f30,f29,f28])).

fof(f28,plain,
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
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2))
              | k1_partfun1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2))
            | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) = k2_struct_0(sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2))
          | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) = k2_struct_0(sK2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
        | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
      & v2_funct_1(sK3)
      & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f37,f56])).

fof(f56,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f90,plain,
    ( k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,
    ( k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f162,plain,(
    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f159,f141])).

fof(f141,plain,(
    v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f136,f95])).

fof(f95,plain,(
    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f94,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f92,f75])).

fof(f75,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f66,f72])).

fof(f72,plain,(
    k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f63,f71])).

fof(f71,plain,(
    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f47,f65])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f63,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f61,f57])).

fof(f61,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f38,f56])).

fof(f38,plain,(
    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f58,f57])).

fof(f58,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f36,f56])).

fof(f36,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) ),
    inference(backward_demodulation,[],[f65,f72])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f21,f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f136,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(superposition,[],[f48,f113])).

fof(f113,plain,(
    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f111,f75])).

fof(f111,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f110,f74])).

fof(f110,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f109,plain,
    ( ~ v2_funct_1(sK3)
    | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f52,f78])).

fof(f78,plain,(
    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f159,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f154,f139])).

fof(f139,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f134,f95])).

% (14478)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f134,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1))))
    | ~ sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(superposition,[],[f50,f113])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f151,f35])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f53,f74])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f119,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))
    | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) ),
    inference(forward_demodulation,[],[f118,f113])).

fof(f118,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)
    | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(backward_demodulation,[],[f79,f113])).

fof(f79,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3) ),
    inference(forward_demodulation,[],[f77,f72])).

fof(f77,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3)
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f70,f72])).

fof(f70,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3))
    | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3) ),
    inference(backward_demodulation,[],[f67,f69])).

fof(f69,plain,(
    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f46,f65])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f67,plain,
    ( k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3)
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f64,f57])).

fof(f64,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) ),
    inference(backward_demodulation,[],[f62,f57])).

fof(f62,plain,
    ( k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3)
    | k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f60,f56])).

fof(f60,plain,
    ( k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f55,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(backward_demodulation,[],[f54,f38])).

fof(f54,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(definition_unfolding,[],[f40,f41,f41])).

fof(f41,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f40,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f176,plain,(
    k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f175,f88])).

fof(f88,plain,(
    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f87,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f86,f35])).

fof(f86,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f175,plain,(
    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f172,f35])).

fof(f172,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f156,f74])).

fof(f156,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3))
      | ~ v1_funct_1(X11) ) ),
    inference(subsumption_resolution,[],[f153,f141])).

fof(f153,plain,(
    ! [X10,X11,X9] :
      ( k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3))
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11) ) ),
    inference(resolution,[],[f53,f139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (14488)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (14483)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (14475)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (14483)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f176,f165])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK3)) | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.47    inference(backward_demodulation,[],[f119,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK3)) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)),
% 0.20/0.47    inference(forward_demodulation,[],[f162,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f90,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    v1_relat_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f45,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 0.20/0.47    inference(backward_demodulation,[],[f59,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.47    inference(resolution,[],[f42,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    l1_struct_0(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    (((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f30,f29,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ? [X2] : ((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => ((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 0.20/0.47    inference(backward_demodulation,[],[f37,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.47    inference(resolution,[],[f42,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    l1_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_relat_1(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f89,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f44,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    v2_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f159,f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.47    inference(subsumption_resolution,[],[f136,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f94,f35])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f92,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))),
% 0.20/0.47    inference(backward_demodulation,[],[f66,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    k2_struct_0(sK2) = k2_relat_1(sK3)),
% 0.20/0.47    inference(backward_demodulation,[],[f63,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f47,f65])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 0.20/0.47    inference(backward_demodulation,[],[f61,f57])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.20/0.47    inference(backward_demodulation,[],[f38,f56])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.20/0.47    inference(backward_demodulation,[],[f58,f57])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.47    inference(backward_demodulation,[],[f36,f56])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f51,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))),
% 0.20/0.47    inference(backward_demodulation,[],[f65,f72])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (sP0(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(definition_folding,[],[f21,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    v1_funct_1(k2_funct_1(sK3)) | ~sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.47    inference(superposition,[],[f48,f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f112,f35])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f111,f75])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f110,f74])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f109,f39])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ~v2_funct_1(sK3) | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    k2_relat_1(sK3) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.47    inference(superposition,[],[f52,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.47    inference(backward_demodulation,[],[f71,f72])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f26])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.47    inference(resolution,[],[f154,f139])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1))))),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f95])).
% 0.20/0.47  % (14478)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) | ~sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.47    inference(superposition,[],[f50,f113])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f151,f35])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(resolution,[],[f53,f74])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)),
% 0.20/0.48    inference(forward_demodulation,[],[f118,f113])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.20/0.48    inference(backward_demodulation,[],[f79,f113])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3)),
% 0.20/0.48    inference(forward_demodulation,[],[f77,f72])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3) | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3))),
% 0.20/0.48    inference(backward_demodulation,[],[f70,f72])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3)) | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f67,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f46,f65])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3) | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f64,f57])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f62,f57])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) | k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f60,f56])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2))),
% 0.20/0.48    inference(backward_demodulation,[],[f55,f56])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.48    inference(backward_demodulation,[],[f54,f38])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.48    inference(definition_unfolding,[],[f40,f41,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f175,f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f87,f68])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f86,f35])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f43,f39])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f172,f35])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f156,f74])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ( ! [X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3)) | ~v1_funct_1(X11)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f153,f141])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ( ! [X10,X11,X9] : (k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(X11)) )),
% 0.20/0.48    inference(resolution,[],[f53,f139])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (14483)------------------------------
% 0.20/0.48  % (14483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (14483)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (14483)Memory used [KB]: 10746
% 0.20/0.48  % (14483)Time elapsed: 0.016 s
% 0.20/0.48  % (14483)------------------------------
% 0.20/0.48  % (14483)------------------------------
% 0.20/0.48  % (14472)Success in time 0.117 s
%------------------------------------------------------------------------------
