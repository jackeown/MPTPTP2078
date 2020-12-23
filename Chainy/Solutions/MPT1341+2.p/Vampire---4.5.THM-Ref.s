%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1341+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 7.91s
% Output     : Refutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 973 expanded)
%              Number of leaves         :   15 ( 362 expanded)
%              Depth                    :   18
%              Number of atoms          :  348 (8224 expanded)
%              Number of equality atoms :  107 (2899 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9746,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f9610,f9673,f9739])).

fof(f9739,plain,(
    spl291_2 ),
    inference(avatar_contradiction_clause,[],[f9738])).

fof(f9738,plain,
    ( $false
    | spl291_2 ),
    inference(subsumption_resolution,[],[f9737,f4082])).

fof(f4082,plain,(
    v1_funct_1(sK70) ),
    inference(cnf_transformation,[],[f3466])).

fof(f3466,plain,
    ( ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),sK70) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70))
      | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) )
    & v2_funct_1(sK70)
    & k2_struct_0(sK69) = k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)
    & m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
    & v1_funct_2(sK70,u1_struct_0(sK68),u1_struct_0(sK69))
    & v1_funct_1(sK70)
    & l1_struct_0(sK69)
    & l1_struct_0(sK68) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK68,sK69,sK70])],[f2468,f3465,f3464,f3463])).

fof(f3463,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK68),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(sK68),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK68),X2,k2_tops_2(u1_struct_0(sK68),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK68),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK68),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK68) ) ),
    introduced(choice_axiom,[])).

fof(f3464,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK68),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(X1),X2))
              | k1_partfun1(u1_struct_0(sK68),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK68),X2,k2_tops_2(u1_struct_0(sK68),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK68),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK68),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),X2))
            | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),X2,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),X2)) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),X2) = k2_struct_0(sK69)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
          & v1_funct_2(X2,u1_struct_0(sK68),u1_struct_0(sK69))
          & v1_funct_1(X2) )
      & l1_struct_0(sK69) ) ),
    introduced(choice_axiom,[])).

fof(f3465,plain,
    ( ? [X2] :
        ( ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),X2))
          | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),X2,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),X2)) )
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),X2) = k2_struct_0(sK69)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
        & v1_funct_2(X2,u1_struct_0(sK68),u1_struct_0(sK69))
        & v1_funct_1(X2) )
   => ( ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),sK70) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70))
        | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) )
      & v2_funct_1(sK70)
      & k2_struct_0(sK69) = k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)
      & m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
      & v1_funct_2(sK70,u1_struct_0(sK68),u1_struct_0(sK69))
      & v1_funct_1(sK70) ) ),
    introduced(choice_axiom,[])).

fof(f2468,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2467])).

fof(f2467,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2413])).

fof(f2413,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                 => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2412])).

fof(f2412,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

fof(f9737,plain,
    ( ~ v1_funct_1(sK70)
    | spl291_2 ),
    inference(subsumption_resolution,[],[f9736,f6911])).

fof(f6911,plain,(
    m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70)))) ),
    inference(backward_demodulation,[],[f4084,f6909])).

fof(f6909,plain,(
    u1_struct_0(sK69) = k2_relat_1(sK70) ),
    inference(backward_demodulation,[],[f5603,f6570])).

fof(f6570,plain,(
    k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k2_relat_1(sK70) ),
    inference(resolution,[],[f4084,f4260])).

fof(f4260,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2570])).

fof(f2570,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f5603,plain,(
    u1_struct_0(sK69) = k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70) ),
    inference(backward_demodulation,[],[f4085,f5592])).

fof(f5592,plain,(
    u1_struct_0(sK69) = k2_struct_0(sK69) ),
    inference(resolution,[],[f4081,f4267])).

fof(f4267,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2577])).

fof(f2577,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f4081,plain,(
    l1_struct_0(sK69) ),
    inference(cnf_transformation,[],[f3466])).

fof(f4085,plain,(
    k2_struct_0(sK69) = k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70) ),
    inference(cnf_transformation,[],[f3466])).

fof(f4084,plain,(
    m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69)))) ),
    inference(cnf_transformation,[],[f3466])).

fof(f9736,plain,
    ( ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70))))
    | ~ v1_funct_1(sK70)
    | spl291_2 ),
    inference(subsumption_resolution,[],[f9735,f6345])).

fof(f6345,plain,(
    v1_funct_1(k2_funct_1(sK70)) ),
    inference(forward_demodulation,[],[f6344,f6336])).

fof(f6336,plain,(
    k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k2_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f6335,f4082])).

fof(f6335,plain,
    ( k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k2_funct_1(sK70)
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f6334,f4084])).

fof(f6334,plain,
    ( k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k2_funct_1(sK70)
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f6333,f5603])).

fof(f6333,plain,
    ( k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k2_funct_1(sK70)
    | u1_struct_0(sK69) != k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f6165,f4086])).

fof(f4086,plain,(
    v2_funct_1(sK70) ),
    inference(cnf_transformation,[],[f3466])).

fof(f6165,plain,
    ( k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k2_funct_1(sK70)
    | ~ v2_funct_1(sK70)
    | u1_struct_0(sK69) != k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
    | ~ v1_funct_1(sK70) ),
    inference(resolution,[],[f4083,f4182])).

fof(f4182,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2523])).

fof(f2523,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2522])).

fof(f2522,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2245])).

fof(f2245,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f4083,plain,(
    v1_funct_2(sK70,u1_struct_0(sK68),u1_struct_0(sK69)) ),
    inference(cnf_transformation,[],[f3466])).

fof(f6344,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) ),
    inference(subsumption_resolution,[],[f6343,f4082])).

fof(f6343,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70))
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f6166,f4084])).

fof(f6166,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70))
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
    | ~ v1_funct_1(sK70) ),
    inference(resolution,[],[f4083,f4183])).

fof(f4183,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2525])).

fof(f2525,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2524])).

fof(f2524,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2252])).

fof(f2252,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f9735,plain,
    ( ~ v1_funct_1(k2_funct_1(sK70))
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70))))
    | ~ v1_funct_1(sK70)
    | spl291_2 ),
    inference(subsumption_resolution,[],[f9734,f6955])).

fof(f6955,plain,(
    m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68)))) ),
    inference(backward_demodulation,[],[f6351,f6909])).

fof(f6351,plain,(
    m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK69),u1_struct_0(sK68)))) ),
    inference(forward_demodulation,[],[f6350,f6336])).

fof(f6350,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK69),u1_struct_0(sK68)))) ),
    inference(subsumption_resolution,[],[f6349,f4082])).

fof(f6349,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK69),u1_struct_0(sK68))))
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f6168,f4084])).

fof(f6168,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK69),u1_struct_0(sK68))))
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),u1_struct_0(sK69))))
    | ~ v1_funct_1(sK70) ),
    inference(resolution,[],[f4083,f4185])).

fof(f4185,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2525])).

fof(f9734,plain,
    ( ~ m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68))))
    | ~ v1_funct_1(k2_funct_1(sK70))
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70))))
    | ~ v1_funct_1(sK70)
    | spl291_2 ),
    inference(subsumption_resolution,[],[f9698,f8710])).

fof(f8710,plain,(
    k5_relat_1(sK70,k2_funct_1(sK70)) = k6_partfun1(k1_relat_1(sK70)) ),
    inference(subsumption_resolution,[],[f8709,f4082])).

fof(f8709,plain,
    ( k5_relat_1(sK70,k2_funct_1(sK70)) = k6_partfun1(k1_relat_1(sK70))
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f8429,f4086])).

fof(f8429,plain,
    ( k5_relat_1(sK70,k2_funct_1(sK70)) = k6_partfun1(k1_relat_1(sK70))
    | ~ v2_funct_1(sK70)
    | ~ v1_funct_1(sK70) ),
    inference(resolution,[],[f6576,f5398])).

fof(f5398,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f4337,f4098])).

fof(f4098,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f1558])).

fof(f1558,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f4337,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2630])).

fof(f2630,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2629])).

fof(f2629,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1032])).

fof(f1032,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f6576,plain,(
    v1_relat_1(sK70) ),
    inference(resolution,[],[f4084,f4273])).

fof(f4273,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2585])).

fof(f2585,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f9698,plain,
    ( k5_relat_1(sK70,k2_funct_1(sK70)) != k6_partfun1(k1_relat_1(sK70))
    | ~ m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68))))
    | ~ v1_funct_1(k2_funct_1(sK70))
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70))))
    | ~ v1_funct_1(sK70)
    | spl291_2 ),
    inference(superposition,[],[f9609,f4148])).

fof(f4148,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f2509])).

fof(f2509,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f2508])).

fof(f2508,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1552])).

fof(f1552,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f9609,plain,
    ( k6_partfun1(k1_relat_1(sK70)) != k1_partfun1(u1_struct_0(sK68),k2_relat_1(sK70),k2_relat_1(sK70),u1_struct_0(sK68),sK70,k2_funct_1(sK70))
    | spl291_2 ),
    inference(avatar_component_clause,[],[f9608])).

fof(f9608,plain,
    ( spl291_2
  <=> k6_partfun1(k1_relat_1(sK70)) = k1_partfun1(u1_struct_0(sK68),k2_relat_1(sK70),k2_relat_1(sK70),u1_struct_0(sK68),sK70,k2_funct_1(sK70)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl291_2])])).

fof(f9673,plain,(
    spl291_1 ),
    inference(avatar_contradiction_clause,[],[f9672])).

fof(f9672,plain,
    ( $false
    | spl291_1 ),
    inference(subsumption_resolution,[],[f9671,f6345])).

fof(f9671,plain,
    ( ~ v1_funct_1(k2_funct_1(sK70))
    | spl291_1 ),
    inference(subsumption_resolution,[],[f9670,f6955])).

fof(f9670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68))))
    | ~ v1_funct_1(k2_funct_1(sK70))
    | spl291_1 ),
    inference(subsumption_resolution,[],[f9669,f4082])).

fof(f9669,plain,
    ( ~ v1_funct_1(sK70)
    | ~ m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68))))
    | ~ v1_funct_1(k2_funct_1(sK70))
    | spl291_1 ),
    inference(subsumption_resolution,[],[f9668,f6911])).

fof(f9668,plain,
    ( ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70))))
    | ~ v1_funct_1(sK70)
    | ~ m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68))))
    | ~ v1_funct_1(k2_funct_1(sK70))
    | spl291_1 ),
    inference(subsumption_resolution,[],[f9631,f8703])).

fof(f8703,plain,(
    k5_relat_1(k2_funct_1(sK70),sK70) = k6_partfun1(k2_relat_1(sK70)) ),
    inference(subsumption_resolution,[],[f8702,f4082])).

fof(f8702,plain,
    ( k5_relat_1(k2_funct_1(sK70),sK70) = k6_partfun1(k2_relat_1(sK70))
    | ~ v1_funct_1(sK70) ),
    inference(subsumption_resolution,[],[f8428,f4086])).

fof(f8428,plain,
    ( k5_relat_1(k2_funct_1(sK70),sK70) = k6_partfun1(k2_relat_1(sK70))
    | ~ v2_funct_1(sK70)
    | ~ v1_funct_1(sK70) ),
    inference(resolution,[],[f6576,f5397])).

fof(f5397,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f4338,f4098])).

fof(f4338,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2630])).

fof(f9631,plain,
    ( k5_relat_1(k2_funct_1(sK70),sK70) != k6_partfun1(k2_relat_1(sK70))
    | ~ m1_subset_1(sK70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK68),k2_relat_1(sK70))))
    | ~ v1_funct_1(sK70)
    | ~ m1_subset_1(k2_funct_1(sK70),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK70),u1_struct_0(sK68))))
    | ~ v1_funct_1(k2_funct_1(sK70))
    | spl291_1 ),
    inference(superposition,[],[f9606,f4148])).

fof(f9606,plain,
    ( k6_partfun1(k2_relat_1(sK70)) != k1_partfun1(k2_relat_1(sK70),u1_struct_0(sK68),u1_struct_0(sK68),k2_relat_1(sK70),k2_funct_1(sK70),sK70)
    | spl291_1 ),
    inference(avatar_component_clause,[],[f9605])).

fof(f9605,plain,
    ( spl291_1
  <=> k6_partfun1(k2_relat_1(sK70)) = k1_partfun1(k2_relat_1(sK70),u1_struct_0(sK68),u1_struct_0(sK68),k2_relat_1(sK70),k2_funct_1(sK70),sK70) ),
    introduced(avatar_definition,[new_symbols(naming,[spl291_1])])).

fof(f9610,plain,
    ( ~ spl291_1
    | ~ spl291_2 ),
    inference(avatar_split_clause,[],[f7222,f9608,f9605])).

fof(f7222,plain,
    ( k6_partfun1(k1_relat_1(sK70)) != k1_partfun1(u1_struct_0(sK68),k2_relat_1(sK70),k2_relat_1(sK70),u1_struct_0(sK68),sK70,k2_funct_1(sK70))
    | k6_partfun1(k2_relat_1(sK70)) != k1_partfun1(k2_relat_1(sK70),u1_struct_0(sK68),u1_struct_0(sK68),k2_relat_1(sK70),k2_funct_1(sK70),sK70) ),
    inference(forward_demodulation,[],[f7024,f6909])).

fof(f7024,plain,
    ( k6_partfun1(k2_relat_1(sK70)) != k1_partfun1(k2_relat_1(sK70),u1_struct_0(sK68),u1_struct_0(sK68),k2_relat_1(sK70),k2_funct_1(sK70),sK70)
    | k6_partfun1(k1_relat_1(sK70)) != k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_funct_1(sK70)) ),
    inference(backward_demodulation,[],[f6860,f6909])).

fof(f6860,plain,
    ( k6_partfun1(k1_relat_1(sK70)) != k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_funct_1(sK70))
    | k6_partfun1(u1_struct_0(sK69)) != k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_funct_1(sK70),sK70) ),
    inference(backward_demodulation,[],[f6342,f6523])).

fof(f6523,plain,(
    k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70) = k1_relat_1(sK70) ),
    inference(resolution,[],[f4084,f4137])).

fof(f4137,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2498])).

fof(f2498,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f6342,plain,
    ( k6_partfun1(u1_struct_0(sK69)) != k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_funct_1(sK70),sK70)
    | k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_funct_1(sK70)) ),
    inference(forward_demodulation,[],[f6341,f6336])).

fof(f6341,plain,
    ( k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_funct_1(sK70))
    | k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),sK70) != k6_partfun1(u1_struct_0(sK69)) ),
    inference(backward_demodulation,[],[f5604,f6336])).

fof(f5604,plain,
    ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),sK70) != k6_partfun1(u1_struct_0(sK69))
    | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) ),
    inference(backward_demodulation,[],[f5543,f5592])).

fof(f5543,plain,
    ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),sK70) != k6_partfun1(k2_struct_0(sK69))
    | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) ),
    inference(backward_demodulation,[],[f4087,f4085])).

fof(f4087,plain,
    ( k1_partfun1(u1_struct_0(sK69),u1_struct_0(sK68),u1_struct_0(sK68),u1_struct_0(sK69),k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70),sK70) != k6_partfun1(k2_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70))
    | k1_partfun1(u1_struct_0(sK68),u1_struct_0(sK69),u1_struct_0(sK69),u1_struct_0(sK68),sK70,k2_tops_2(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) != k6_partfun1(k1_relset_1(u1_struct_0(sK68),u1_struct_0(sK69),sK70)) ),
    inference(cnf_transformation,[],[f3466])).
%------------------------------------------------------------------------------
