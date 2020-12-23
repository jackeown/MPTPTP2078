%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 (4021 expanded)
%              Number of leaves         :   15 (1455 expanded)
%              Depth                    :   25
%              Number of atoms          :  348 (30732 expanded)
%              Number of equality atoms :  123 (11111 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f180,f169])).

fof(f169,plain,(
    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK3))
    | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f123,f167])).

fof(f167,plain,(
    k6_relat_1(k2_relat_1(sK3)) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) ),
    inference(forward_demodulation,[],[f166,f95])).

fof(f95,plain,(
    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f94,f71])).

fof(f71,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) ),
    inference(resolution,[],[f44,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f61,f59])).

fof(f59,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
      | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
    & v2_funct_1(sK3)
    & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_2)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f38,f58])).

fof(f58,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f94,plain,
    ( k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f93,f36])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,
    ( k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f166,plain,(
    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f163,f145])).

fof(f145,plain,(
    v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f140,f99])).

fof(f99,plain,(
    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f96,f78])).

fof(f78,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f68,f75])).

fof(f75,plain,(
    k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f65,f74])).

fof(f74,plain,(
    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f49,f67])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f65,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f63,f59])).

fof(f63,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f39,f58])).

fof(f39,plain,(
    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f60,f59])).

fof(f60,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f37,f58])).

fof(f37,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f53,f77])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) ),
    inference(backward_demodulation,[],[f67,f75])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f140,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(superposition,[],[f50,f117])).

fof(f117,plain,(
    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f116,f36])).

fof(f116,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f115,f78])).

fof(f115,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f114,f77])).

fof(f114,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,
    ( ~ v2_funct_1(sK3)
    | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f54,f81])).

fof(f81,plain,(
    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f74,f75])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f163,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f158,f143])).

fof(f143,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f138,f99])).

fof(f138,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1))))
    | ~ sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(superposition,[],[f52,f117])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f155,f36])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f55,f77])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f123,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))
    | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) ),
    inference(forward_demodulation,[],[f122,f117])).

fof(f122,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)
    | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(backward_demodulation,[],[f82,f117])).

fof(f82,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3) ),
    inference(forward_demodulation,[],[f80,f75])).

fof(f80,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3)
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f73,f75])).

fof(f73,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3))
    | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3) ),
    inference(backward_demodulation,[],[f69,f72])).

fof(f72,plain,(
    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f48,f67])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,
    ( k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3)
    | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f66,f59])).

fof(f66,plain,
    ( k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) ),
    inference(backward_demodulation,[],[f64,f59])).

fof(f64,plain,
    ( k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3)
    | k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f62,f58])).

fof(f62,plain,
    ( k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f57,f58])).

fof(f57,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(backward_demodulation,[],[f56,f39])).

fof(f56,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(definition_unfolding,[],[f41,f42,f42])).

fof(f42,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f41,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f180,plain,(
    k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f179,f92])).

fof(f92,plain,(
    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f91,f71])).

fof(f91,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f90,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f45,f40])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f179,plain,(
    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f176,f36])).

fof(f176,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f160,f77])).

fof(f160,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3))
      | ~ v1_funct_1(X11) ) ),
    inference(subsumption_resolution,[],[f157,f145])).

fof(f157,plain,(
    ! [X10,X11,X9] :
      ( k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3))
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11) ) ),
    inference(resolution,[],[f55,f143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (15699)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.41  % (15699)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f181,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f180,f169])).
% 0.20/0.41  fof(f169,plain,(
% 0.20/0.41    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f168])).
% 0.20/0.41  fof(f168,plain,(
% 0.20/0.41    k6_relat_1(k2_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK3)) | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.41    inference(backward_demodulation,[],[f123,f167])).
% 0.20/0.41  fof(f167,plain,(
% 0.20/0.41    k6_relat_1(k2_relat_1(sK3)) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)),
% 0.20/0.41    inference(forward_demodulation,[],[f166,f95])).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 0.20/0.41    inference(subsumption_resolution,[],[f94,f71])).
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    v1_relat_1(sK3)),
% 0.20/0.41    inference(subsumption_resolution,[],[f70,f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))),
% 0.20/0.41    inference(resolution,[],[f44,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 0.20/0.42    inference(backward_demodulation,[],[f61,f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.42    inference(resolution,[],[f43,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    l1_struct_0(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    (((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f31,f30,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ? [X2] : ((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),X2,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => ((k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.42    inference(negated_conjecture,[],[f11])).
% 0.20/0.42  fof(f11,conjecture,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_2)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 0.20/0.42    inference(backward_demodulation,[],[f38,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.42    inference(resolution,[],[f43,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    l1_struct_0(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_relat_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f93,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    v1_funct_1(sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    k6_relat_1(k2_relat_1(sK3)) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f46,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    v2_funct_1(sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.42  fof(f166,plain,(
% 0.20/0.42    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f163,f145])).
% 0.20/0.42  fof(f145,plain,(
% 0.20/0.42    v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f140,f99])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f98,f36])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f96,f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))),
% 0.20/0.42    inference(backward_demodulation,[],[f68,f75])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    k2_struct_0(sK2) = k2_relat_1(sK3)),
% 0.20/0.42    inference(backward_demodulation,[],[f65,f74])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f49,f67])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 0.20/0.42    inference(backward_demodulation,[],[f63,f59])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.20/0.42    inference(backward_demodulation,[],[f39,f58])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.20/0.42    inference(backward_demodulation,[],[f60,f59])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.42    inference(backward_demodulation,[],[f37,f58])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f96,plain,(
% 0.20/0.42    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f53,f77])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))),
% 0.20/0.42    inference(backward_demodulation,[],[f67,f75])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (sP0(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.42    inference(definition_folding,[],[f22,f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.42    inference(flattening,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.42  fof(f140,plain,(
% 0.20/0.42    v1_funct_1(k2_funct_1(sK3)) | ~sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.42    inference(superposition,[],[f50,f117])).
% 0.20/0.42  fof(f117,plain,(
% 0.20/0.42    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f116,f36])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f115,f78])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f114,f77])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f113,f40])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    ~v2_funct_1(sK3) | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f110])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    k2_relat_1(sK3) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(superposition,[],[f54,f81])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.42    inference(backward_demodulation,[],[f74,f75])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.42    inference(flattening,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.42    inference(nnf_transformation,[],[f27])).
% 0.20/0.42  fof(f163,plain,(
% 0.20/0.42    k5_relat_1(k2_funct_1(sK3),sK3) = k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.42    inference(resolution,[],[f158,f143])).
% 0.20/0.42  fof(f143,plain,(
% 0.20/0.42    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1))))),
% 0.20/0.42    inference(subsumption_resolution,[],[f138,f99])).
% 0.20/0.42  fof(f138,plain,(
% 0.20/0.42    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) | ~sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.42    inference(superposition,[],[f52,f117])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP0(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f33])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3) | ~v1_funct_1(X2)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f155,f36])).
% 0.20/0.42  fof(f155,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK1),k2_relat_1(sK3),X2,sK3) = k5_relat_1(X2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.42    inference(resolution,[],[f55,f77])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.42    inference(flattening,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3)),
% 0.20/0.42    inference(forward_demodulation,[],[f122,f117])).
% 0.20/0.42  fof(f122,plain,(
% 0.20/0.42    k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_funct_1(sK3),sK3) | k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.20/0.42    inference(backward_demodulation,[],[f82,f117])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    k6_relat_1(k1_relat_1(sK3)) != k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3)),
% 0.20/0.42    inference(forward_demodulation,[],[f80,f75])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    k6_relat_1(k2_relat_1(sK3)) != k1_partfun1(k2_relat_1(sK3),k2_struct_0(sK1),k2_struct_0(sK1),k2_relat_1(sK3),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3),sK3) | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3))),
% 0.20/0.42    inference(backward_demodulation,[],[f73,f75])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relat_1(sK3)) | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3)),
% 0.20/0.42    inference(backward_demodulation,[],[f69,f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f48,f67])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),sK3) | k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.20/0.42    inference(forward_demodulation,[],[f66,f59])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK2),k2_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3)),
% 0.20/0.42    inference(backward_demodulation,[],[f64,f59])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    k6_relat_1(k2_struct_0(sK2)) != k1_partfun1(u1_struct_0(sK2),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) | k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.42    inference(forward_demodulation,[],[f62,f58])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),k2_struct_0(sK1),sK3,k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2))),
% 0.20/0.42    inference(backward_demodulation,[],[f57,f58])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_struct_0(sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.42    inference(backward_demodulation,[],[f56,f39])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_relat_1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_relat_1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.42    inference(definition_unfolding,[],[f41,f42,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK3) != k6_partfun1(k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != k6_partfun1(k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f180,plain,(
% 0.20/0.42    k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.42    inference(forward_demodulation,[],[f179,f92])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f91,f71])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f90,f36])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    k6_relat_1(k1_relat_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f45,f40])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f179,plain,(
% 0.20/0.42    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3))),
% 0.20/0.42    inference(subsumption_resolution,[],[f176,f36])).
% 0.20/0.42  fof(f176,plain,(
% 0.20/0.42    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(k2_struct_0(sK1),k2_relat_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1),sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f160,f77])).
% 0.20/0.42  fof(f160,plain,(
% 0.20/0.42    ( ! [X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3)) | ~v1_funct_1(X11)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f157,f145])).
% 0.20/0.42  fof(f157,plain,(
% 0.20/0.42    ( ! [X10,X11,X9] : (k1_partfun1(X9,X10,k2_relat_1(sK3),k2_struct_0(sK1),X11,k2_funct_1(sK3)) = k5_relat_1(X11,k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(X11)) )),
% 0.20/0.42    inference(resolution,[],[f55,f143])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (15699)------------------------------
% 0.20/0.42  % (15699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (15699)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (15699)Memory used [KB]: 10746
% 0.20/0.42  % (15699)Time elapsed: 0.011 s
% 0.20/0.42  % (15699)------------------------------
% 0.20/0.42  % (15699)------------------------------
% 0.20/0.42  % (15689)Success in time 0.065 s
%------------------------------------------------------------------------------
