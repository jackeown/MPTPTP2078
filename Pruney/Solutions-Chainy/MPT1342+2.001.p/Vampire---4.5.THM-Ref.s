%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:36 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  428 (4844 expanded)
%              Number of leaves         :   59 (2206 expanded)
%              Depth                    :   43
%              Number of atoms          : 1666 (73771 expanded)
%              Number of equality atoms :  223 (15260 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f699,f813,f859,f871,f889,f1081,f1200,f1304,f1851,f2052,f2056,f2187,f2218,f2254,f2302,f2456,f3125,f3194,f3232,f3271,f3278,f3332,f3543,f3646,f3654,f3688])).

fof(f3688,plain,
    ( spl10_124
    | ~ spl10_132 ),
    inference(avatar_contradiction_clause,[],[f3687])).

fof(f3687,plain,
    ( $false
    | spl10_124
    | ~ spl10_132 ),
    inference(subsumption_resolution,[],[f3686,f3353])).

fof(f3353,plain,
    ( sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ spl10_132 ),
    inference(avatar_component_clause,[],[f3351])).

fof(f3351,plain,
    ( spl10_132
  <=> sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f3686,plain,
    ( ~ sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | spl10_124 ),
    inference(resolution,[],[f3170,f612])).

fof(f612,plain,(
    ! [X4,X5,X3] :
      ( r2_funct_2(X3,X4,k2_funct_1(X5),k2_funct_1(X5))
      | ~ sP4(X4,X3,X5) ) ),
    inference(subsumption_resolution,[],[f611,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f611,plain,(
    ! [X4,X5,X3] :
      ( r2_funct_2(X3,X4,k2_funct_1(X5),k2_funct_1(X5))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ sP4(X4,X3,X5) ) ),
    inference(subsumption_resolution,[],[f604,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f604,plain,(
    ! [X4,X5,X3] :
      ( r2_funct_2(X3,X4,k2_funct_1(X5),k2_funct_1(X5))
      | ~ v1_funct_2(k2_funct_1(X5),X3,X4)
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ sP4(X4,X3,X5) ) ),
    inference(resolution,[],[f151,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f151,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f3170,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | spl10_124 ),
    inference(avatar_component_clause,[],[f3168])).

fof(f3168,plain,
    ( spl10_124
  <=> r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f3654,plain,(
    spl10_119 ),
    inference(avatar_contradiction_clause,[],[f3653])).

fof(f3653,plain,
    ( $false
    | spl10_119 ),
    inference(subsumption_resolution,[],[f3652,f205])).

fof(f205,plain,(
    v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f198,f112])).

fof(f112,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f198,plain,
    ( v1_relat_1(sK8)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) ),
    inference(resolution,[],[f108,f90])).

fof(f90,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK9)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8)))
    & v2_funct_1(sK9)
    & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9)
    & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9)
    & v2_funct_1(sK8)
    & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK8)
    & l1_struct_0(sK7)
    & ~ v2_struct_0(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f27,f71,f70,f69,f68,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3)))
                        & v2_funct_1(X4)
                        & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                        & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                        & v2_funct_1(X3)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & l1_struct_0(X2)
                & ~ v2_struct_0(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X3)))
                      & v2_funct_1(X4)
                      & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                      & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                      & v2_funct_1(X3)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_struct_0(X2)
              & ~ v2_struct_0(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X3)))
                    & v2_funct_1(X4)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                    & v2_funct_1(X3)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & l1_struct_0(X2)
            & ~ v2_struct_0(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3)))
                  & v2_funct_1(X4)
                  & k2_struct_0(X2) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4)
                  & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4)
                  & v2_funct_1(X3)
                  & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
              & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6))
              & v1_funct_1(X3) )
          & l1_struct_0(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3)))
                & v2_funct_1(X4)
                & k2_struct_0(X2) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4)
                & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4)
                & v2_funct_1(X3)
                & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X2))))
                & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X2))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
            & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6))
            & v1_funct_1(X3) )
        & l1_struct_0(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),X3,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3)))
              & v2_funct_1(X4)
              & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7)
              & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4)
              & v2_funct_1(X3)
              & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
              & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
          & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6))
          & v1_funct_1(X3) )
      & l1_struct_0(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),X3,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3)))
            & v2_funct_1(X4)
            & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7)
            & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4)
            & v2_funct_1(X3)
            & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
            & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8)))
          & v2_funct_1(X4)
          & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7)
          & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4)
          & v2_funct_1(sK8)
          & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
          & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7))
          & v1_funct_1(X4) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8)))
        & v2_funct_1(X4)
        & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7)
        & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4)
        & v2_funct_1(sK8)
        & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
        & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7))
        & v1_funct_1(X4) )
   => ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK9)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8)))
      & v2_funct_1(sK9)
      & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9)
      & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9)
      & v2_funct_1(sK8)
      & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
      & v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3)))
                      & v2_funct_1(X4)
                      & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                      & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                      & v2_funct_1(X3)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_struct_0(X2)
              & ~ v2_struct_0(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3)))
                      & v2_funct_1(X4)
                      & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                      & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                      & v2_funct_1(X3)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_struct_0(X2)
              & ~ v2_struct_0(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_struct_0(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( ( v2_funct_1(X4)
                            & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                            & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                            & v2_funct_1(X3)
                            & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_struct_0(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                     => ( ( v2_funct_1(X4)
                          & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                          & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)
                          & v2_funct_1(X3)
                          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tops_2)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f3652,plain,
    ( ~ v1_relat_1(sK8)
    | spl10_119 ),
    inference(subsumption_resolution,[],[f3651,f88])).

fof(f88,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f3651,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl10_119 ),
    inference(subsumption_resolution,[],[f3650,f206])).

fof(f206,plain,(
    v1_relat_1(sK9) ),
    inference(subsumption_resolution,[],[f199,f112])).

fof(f199,plain,
    ( v1_relat_1(sK9)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))) ),
    inference(resolution,[],[f108,f93])).

fof(f93,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f72])).

fof(f3650,plain,
    ( ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl10_119 ),
    inference(subsumption_resolution,[],[f3649,f91])).

fof(f91,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f3649,plain,
    ( ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl10_119 ),
    inference(subsumption_resolution,[],[f3648,f95])).

fof(f95,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f3648,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl10_119 ),
    inference(subsumption_resolution,[],[f3647,f98])).

fof(f98,plain,(
    v2_funct_1(sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f3647,plain,
    ( ~ v2_funct_1(sK9)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl10_119 ),
    inference(resolution,[],[f3142,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f3142,plain,
    ( ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | spl10_119 ),
    inference(avatar_component_clause,[],[f3140])).

fof(f3140,plain,
    ( spl10_119
  <=> v2_funct_1(k5_relat_1(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f3646,plain,
    ( ~ spl10_69
    | ~ spl10_117
    | spl10_118 ),
    inference(avatar_contradiction_clause,[],[f3645])).

fof(f3645,plain,
    ( $false
    | ~ spl10_69
    | ~ spl10_117
    | spl10_118 ),
    inference(trivial_inequality_removal,[],[f3644])).

fof(f3644,plain,
    ( k2_relat_1(sK8) != k2_relat_1(sK8)
    | ~ spl10_69
    | ~ spl10_117
    | spl10_118 ),
    inference(resolution,[],[f3642,f144])).

fof(f144,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3642,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK8),X0)
        | k2_relat_1(sK8) != X0 )
    | ~ spl10_69
    | ~ spl10_117
    | spl10_118 ),
    inference(forward_demodulation,[],[f3641,f2036])).

fof(f2036,plain,
    ( k1_relat_1(sK9) = k2_relat_1(sK8)
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f2034])).

fof(f2034,plain,
    ( spl10_69
  <=> k1_relat_1(sK9) = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f3641,plain,
    ( ! [X0] :
        ( k2_relat_1(sK8) != X0
        | ~ r1_tarski(k1_relat_1(sK9),X0) )
    | ~ spl10_117
    | spl10_118 ),
    inference(subsumption_resolution,[],[f3640,f206])).

fof(f3640,plain,
    ( ! [X0] :
        ( k2_relat_1(sK8) != X0
        | ~ r1_tarski(k1_relat_1(sK9),X0)
        | ~ v1_relat_1(sK9) )
    | ~ spl10_117
    | spl10_118 ),
    inference(trivial_inequality_removal,[],[f3638])).

fof(f3638,plain,
    ( ! [X0] :
        ( k2_relat_1(sK9) != k2_relat_1(sK9)
        | k2_relat_1(sK8) != X0
        | ~ r1_tarski(k1_relat_1(sK9),X0)
        | ~ v1_relat_1(sK9) )
    | ~ spl10_117
    | spl10_118 ),
    inference(superposition,[],[f3634,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f3634,plain,
    ( ! [X0] :
        ( k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0))
        | k2_relat_1(sK8) != X0 )
    | ~ spl10_117
    | spl10_118 ),
    inference(forward_demodulation,[],[f3633,f105])).

fof(f105,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f3633,plain,
    ( ! [X0] :
        ( k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK8) )
    | ~ spl10_117
    | spl10_118 ),
    inference(subsumption_resolution,[],[f3632,f206])).

fof(f3632,plain,
    ( ! [X0] :
        ( k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK8)
        | ~ v1_relat_1(sK9) )
    | ~ spl10_117
    | spl10_118 ),
    inference(subsumption_resolution,[],[f3625,f101])).

fof(f101,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f3625,plain,
    ( ! [X0] :
        ( k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK8)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(sK9) )
    | ~ spl10_117
    | spl10_118 ),
    inference(superposition,[],[f3588,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f3588,plain,
    ( ! [X1] :
        ( k2_relat_1(sK9) != k2_relat_1(k5_relat_1(X1,sK9))
        | k2_relat_1(X1) != k2_relat_1(sK8)
        | ~ v1_relat_1(X1) )
    | ~ spl10_117
    | spl10_118 ),
    inference(subsumption_resolution,[],[f3587,f205])).

fof(f3587,plain,
    ( ! [X1] :
        ( k2_relat_1(sK9) != k2_relat_1(k5_relat_1(X1,sK9))
        | k2_relat_1(X1) != k2_relat_1(sK8)
        | ~ v1_relat_1(sK8)
        | ~ v1_relat_1(X1) )
    | ~ spl10_117
    | spl10_118 ),
    inference(subsumption_resolution,[],[f3585,f206])).

fof(f3585,plain,
    ( ! [X1] :
        ( k2_relat_1(sK9) != k2_relat_1(k5_relat_1(X1,sK9))
        | k2_relat_1(X1) != k2_relat_1(sK8)
        | ~ v1_relat_1(sK9)
        | ~ v1_relat_1(sK8)
        | ~ v1_relat_1(X1) )
    | ~ spl10_117
    | spl10_118 ),
    inference(superposition,[],[f3584,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f3584,plain,
    ( k2_relat_1(sK9) != k2_relat_1(k5_relat_1(sK8,sK9))
    | ~ spl10_117
    | spl10_118 ),
    inference(subsumption_resolution,[],[f3583,f3133])).

fof(f3133,plain,
    ( m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ spl10_117 ),
    inference(avatar_component_clause,[],[f3132])).

fof(f3132,plain,
    ( spl10_117
  <=> m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_117])])).

fof(f3583,plain,
    ( k2_relat_1(sK9) != k2_relat_1(k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | spl10_118 ),
    inference(superposition,[],[f3138,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f3138,plain,
    ( k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | spl10_118 ),
    inference(avatar_component_clause,[],[f3136])).

fof(f3136,plain,
    ( spl10_118
  <=> k2_relat_1(sK9) = k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f3543,plain,
    ( spl10_132
    | ~ spl10_119
    | ~ spl10_118
    | ~ spl10_8
    | ~ spl10_116
    | ~ spl10_117 ),
    inference(avatar_split_clause,[],[f3542,f3132,f3128,f778,f3136,f3140,f3351])).

fof(f778,plain,
    ( spl10_8
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f3128,plain,
    ( spl10_116
  <=> v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f3542,plain,
    ( k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ spl10_8
    | ~ spl10_116
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f3541,f855])).

fof(f855,plain,
    ( v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f854,f88])).

fof(f854,plain,
    ( v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ v1_funct_1(sK8)
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f853,f563])).

fof(f563,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8)))) ),
    inference(forward_demodulation,[],[f339,f355])).

fof(f355,plain,(
    k1_relat_1(sK9) = k2_relat_1(sK8) ),
    inference(backward_demodulation,[],[f286,f310])).

fof(f310,plain,(
    k2_struct_0(sK6) = k2_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f294,f90])).

fof(f294,plain,
    ( k2_struct_0(sK6) = k2_relat_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(superposition,[],[f119,f94])).

fof(f94,plain,(
    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f286,plain,(
    k2_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(subsumption_resolution,[],[f278,f93])).

fof(f278,plain,
    ( k2_struct_0(sK6) = k1_relat_1(sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(superposition,[],[f118,f96])).

fof(f96,plain,(
    k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f339,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k1_relat_1(sK9)))) ),
    inference(backward_demodulation,[],[f191,f286])).

fof(f191,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) ),
    inference(subsumption_resolution,[],[f190,f85])).

fof(f85,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f190,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f167,f106])).

fof(f106,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f167,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(subsumption_resolution,[],[f153,f83])).

fof(f83,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f72])).

fof(f153,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_struct_0(sK5) ),
    inference(superposition,[],[f90,f106])).

fof(f853,plain,
    ( v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f852,f91])).

fof(f852,plain,
    ( v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f820,f565])).

fof(f565,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) ),
    inference(forward_demodulation,[],[f564,f355])).

fof(f564,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),k2_relat_1(sK9)))) ),
    inference(forward_demodulation,[],[f340,f311])).

fof(f311,plain,(
    k2_struct_0(sK7) = k2_relat_1(sK9) ),
    inference(subsumption_resolution,[],[f295,f93])).

fof(f295,plain,
    ( k2_struct_0(sK7) = k2_relat_1(sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(superposition,[],[f119,f97])).

fof(f97,plain,(
    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) ),
    inference(cnf_transformation,[],[f72])).

fof(f340,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),k2_struct_0(sK7)))) ),
    inference(backward_demodulation,[],[f195,f286])).

fof(f195,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) ),
    inference(subsumption_resolution,[],[f194,f87])).

fof(f87,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f194,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7))))
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f172,f106])).

fof(f172,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(subsumption_resolution,[],[f158,f85])).

fof(f158,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f93,f106])).

fof(f820,plain,
    ( v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_8 ),
    inference(superposition,[],[f816,f141])).

fof(f141,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f816,plain,
    ( v1_funct_1(k1_partfun1(k2_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f815,f83])).

fof(f815,plain,
    ( v1_funct_1(k1_partfun1(k2_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9))
    | ~ l1_struct_0(sK5)
    | ~ spl10_8 ),
    inference(superposition,[],[f779,f106])).

fof(f779,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f778])).

fof(f3541,plain,
    ( k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ spl10_116
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f3532,f3129])).

fof(f3129,plain,
    ( v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f3128])).

fof(f3532,plain,
    ( k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ spl10_117 ),
    inference(resolution,[],[f3133,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP4(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f48,f65])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f3332,plain,
    ( spl10_117
    | ~ spl10_68
    | ~ spl10_73
    | ~ spl10_77 ),
    inference(avatar_split_clause,[],[f3331,f2085,f2068,f2030,f3132])).

fof(f2030,plain,
    ( spl10_68
  <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f2068,plain,
    ( spl10_73
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f2085,plain,
    ( spl10_77
  <=> m1_subset_1(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f3331,plain,
    ( m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ spl10_68
    | ~ spl10_73
    | ~ spl10_77 ),
    inference(subsumption_resolution,[],[f3330,f88])).

fof(f3330,plain,
    ( m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_73
    | ~ spl10_77 ),
    inference(subsumption_resolution,[],[f3329,f2069])).

fof(f2069,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f2068])).

fof(f3329,plain,
    ( m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_77 ),
    inference(subsumption_resolution,[],[f3328,f91])).

fof(f3328,plain,
    ( m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_77 ),
    inference(subsumption_resolution,[],[f3295,f2031])).

fof(f2031,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f2030])).

fof(f3295,plain,
    ( m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_77 ),
    inference(superposition,[],[f2086,f141])).

fof(f2086,plain,
    ( m1_subset_1(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f2085])).

fof(f3278,plain,
    ( ~ spl10_68
    | ~ spl10_73
    | spl10_77 ),
    inference(avatar_contradiction_clause,[],[f3277])).

fof(f3277,plain,
    ( $false
    | ~ spl10_68
    | ~ spl10_73
    | spl10_77 ),
    inference(subsumption_resolution,[],[f3276,f88])).

fof(f3276,plain,
    ( ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_73
    | spl10_77 ),
    inference(subsumption_resolution,[],[f3275,f2069])).

fof(f3275,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | spl10_77 ),
    inference(subsumption_resolution,[],[f3274,f91])).

fof(f3274,plain,
    ( ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | spl10_77 ),
    inference(subsumption_resolution,[],[f3272,f2031])).

fof(f3272,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_77 ),
    inference(resolution,[],[f2087,f143])).

fof(f143,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f2087,plain,
    ( ~ m1_subset_1(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | spl10_77 ),
    inference(avatar_component_clause,[],[f2085])).

fof(f3271,plain,
    ( spl10_116
    | ~ spl10_68
    | ~ spl10_73
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f3270,f2081,f2068,f2030,f3128])).

fof(f2081,plain,
    ( spl10_76
  <=> v1_funct_2(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f3270,plain,
    ( v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ spl10_68
    | ~ spl10_73
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f3269,f88])).

fof(f3269,plain,
    ( v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_73
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f3268,f2069])).

fof(f3268,plain,
    ( v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f3267,f91])).

fof(f3267,plain,
    ( v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_68
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f3260,f2031])).

fof(f3260,plain,
    ( v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | ~ spl10_76 ),
    inference(superposition,[],[f2082,f141])).

fof(f2082,plain,
    ( v1_funct_2(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f2081])).

fof(f3232,plain,
    ( spl10_76
    | ~ spl10_9
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f3229,f1844,f782,f2081])).

fof(f782,plain,
    ( spl10_9
  <=> v1_funct_2(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f1844,plain,
    ( spl10_61
  <=> u1_struct_0(sK5) = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f3229,plain,
    ( v1_funct_2(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ spl10_9
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f783,f1846])).

fof(f1846,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f1844])).

fof(f783,plain,
    ( v1_funct_2(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f782])).

fof(f3194,plain,
    ( ~ spl10_119
    | ~ spl10_124
    | ~ spl10_118
    | ~ spl10_117
    | ~ spl10_116
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_18
    | ~ spl10_38
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f3193,f1844,f1128,f848,f778,f692,f510,f3128,f3132,f3136,f3168,f3140])).

fof(f510,plain,
    ( spl10_2
  <=> u1_struct_0(sK6) = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f692,plain,
    ( spl10_4
  <=> u1_struct_0(sK7) = k2_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f848,plain,
    ( spl10_18
  <=> r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f1128,plain,
    ( spl10_38
  <=> k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f3193,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_18
    | ~ spl10_38
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f3192,f1846])).

fof(f3192,plain,
    ( ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))
    | k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_18
    | ~ spl10_38
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f3191,f1846])).

fof(f3191,plain,
    ( k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9))))
    | ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_18
    | ~ spl10_38
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f3190,f1846])).

fof(f3190,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | k2_relat_1(sK9) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9))))
    | ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_18
    | ~ spl10_38
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f3189,f1846])).

fof(f3189,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | k2_relat_1(sK9) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9))))
    | ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1799,f855])).

fof(f1799,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(k5_relat_1(sK8,sK9))
    | k2_relat_1(sK9) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9))))
    | ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ v1_funct_1(k5_relat_1(sK8,sK9))
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(superposition,[],[f1797,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f1797,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1796,f205])).

fof(f1796,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v1_relat_1(sK8)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1795,f88])).

fof(f1795,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1794,f206])).

fof(f1794,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1793,f91])).

fof(f1793,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1792,f95])).

fof(f1792,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1790,f98])).

fof(f1790,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))
    | ~ v2_funct_1(sK9)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(superposition,[],[f1787,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(f1787,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8)))
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1786,f91])).

fof(f1786,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8)))
    | ~ v1_funct_1(sK9)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1785,f409])).

fof(f409,plain,(
    v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) ),
    inference(forward_demodulation,[],[f408,f310])).

fof(f408,plain,(
    v1_funct_2(sK9,k2_struct_0(sK6),k2_relat_1(sK9)) ),
    inference(subsumption_resolution,[],[f407,f85])).

fof(f407,plain,
    ( v1_funct_2(sK9,k2_struct_0(sK6),k2_relat_1(sK9))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f362,f106])).

fof(f362,plain,(
    v1_funct_2(sK9,u1_struct_0(sK6),k2_relat_1(sK9)) ),
    inference(backward_demodulation,[],[f179,f311])).

fof(f179,plain,(
    v1_funct_2(sK9,u1_struct_0(sK6),k2_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f165,f87])).

fof(f165,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),k2_struct_0(sK7))
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f92,f106])).

fof(f92,plain,(
    v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f72])).

fof(f1785,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8)))
    | ~ v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1784,f565])).

fof(f1784,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ spl10_2
    | ~ spl10_4
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1783,f1168])).

fof(f1168,plain,
    ( k2_relat_1(sK9) = k2_relset_1(k2_relat_1(sK8),k2_relat_1(sK9),sK9)
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f1043,f512])).

fof(f512,plain,
    ( u1_struct_0(sK6) = k2_relat_1(sK8)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f510])).

fof(f1043,plain,
    ( k2_relat_1(sK9) = k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK9),sK9)
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f359,f693])).

fof(f693,plain,
    ( u1_struct_0(sK7) = k2_relat_1(sK9)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f692])).

fof(f359,plain,(
    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) = k2_relat_1(sK9) ),
    inference(backward_demodulation,[],[f97,f311])).

fof(f1783,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8)))
    | k2_relat_1(sK9) != k2_relset_1(k2_relat_1(sK8),k2_relat_1(sK9),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1781,f98])).

fof(f1781,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8)))
    | ~ v2_funct_1(sK9)
    | k2_relat_1(sK9) != k2_relset_1(k2_relat_1(sK8),k2_relat_1(sK9),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | spl10_18
    | ~ spl10_38 ),
    inference(superposition,[],[f1778,f136])).

fof(f1778,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8)))
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1777,f88])).

fof(f1777,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8)))
    | ~ v1_funct_1(sK8)
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1776,f405])).

fof(f405,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) ),
    inference(forward_demodulation,[],[f329,f355])).

fof(f329,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),k1_relat_1(sK9)) ),
    inference(backward_demodulation,[],[f169,f286])).

fof(f169,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f155,f85])).

fof(f155,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),k2_struct_0(sK6))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f89,f106])).

fof(f89,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f72])).

fof(f1776,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1775,f557])).

fof(f557,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) ),
    inference(forward_demodulation,[],[f330,f355])).

fof(f330,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK9)))) ),
    inference(backward_demodulation,[],[f170,f286])).

fof(f170,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) ),
    inference(subsumption_resolution,[],[f156,f85])).

fof(f156,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f90,f106])).

fof(f1775,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_18
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f1774,f1129])).

fof(f1129,plain,
    ( k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1774,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8)))
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f1767,f95])).

fof(f1767,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8)))
    | ~ v2_funct_1(sK8)
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_18 ),
    inference(superposition,[],[f1443,f136])).

fof(f1443,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | spl10_18 ),
    inference(subsumption_resolution,[],[f1442,f88])).

fof(f1442,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | ~ v1_funct_1(sK8)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f1441,f557])).

fof(f1441,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f1440,f91])).

fof(f1440,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f1435,f565])).

fof(f1435,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_18 ),
    inference(superposition,[],[f850,f141])).

fof(f850,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f848])).

fof(f3125,plain,
    ( spl10_9
    | ~ spl10_61
    | ~ spl10_68
    | ~ spl10_72
    | ~ spl10_73
    | ~ spl10_82 ),
    inference(avatar_contradiction_clause,[],[f3124])).

fof(f3124,plain,
    ( $false
    | spl10_9
    | ~ spl10_61
    | ~ spl10_68
    | ~ spl10_72
    | ~ spl10_73
    | ~ spl10_82 ),
    inference(subsumption_resolution,[],[f3123,f358])).

fof(f358,plain,(
    ~ v1_xboole_0(k2_relat_1(sK8)) ),
    inference(subsumption_resolution,[],[f357,f84])).

fof(f84,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f357,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK8))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f356,f85])).

fof(f356,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK8))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(superposition,[],[f183,f310])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f109,f106])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3123,plain,
    ( v1_xboole_0(k2_relat_1(sK8))
    | spl10_9
    | ~ spl10_61
    | ~ spl10_68
    | ~ spl10_72
    | ~ spl10_73
    | ~ spl10_82 ),
    inference(subsumption_resolution,[],[f3122,f2114])).

fof(f2114,plain,
    ( v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8))
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f2113])).

fof(f2113,plain,
    ( spl10_82
  <=> v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f3122,plain,
    ( ~ v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8))
    | v1_xboole_0(k2_relat_1(sK8))
    | spl10_9
    | ~ spl10_61
    | ~ spl10_68
    | ~ spl10_72
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f3121,f2069])).

fof(f3121,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8))
    | v1_xboole_0(k2_relat_1(sK8))
    | spl10_9
    | ~ spl10_61
    | ~ spl10_68
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f3120,f2049])).

fof(f2049,plain,
    ( v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f2047])).

fof(f2047,plain,
    ( spl10_72
  <=> v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f3120,plain,
    ( ~ v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8))
    | v1_xboole_0(k2_relat_1(sK8))
    | spl10_9
    | ~ spl10_61
    | ~ spl10_68 ),
    inference(resolution,[],[f2559,f2031])).

fof(f2559,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK9))))
        | ~ v1_funct_2(sK9,X0,k2_relat_1(sK9))
        | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0)))
        | ~ v1_funct_2(sK8,k1_relat_1(sK8),X0)
        | v1_xboole_0(X0) )
    | spl10_9
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f2558,f88])).

fof(f2558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK9))))
        | ~ v1_funct_2(sK9,X0,k2_relat_1(sK9))
        | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0)))
        | ~ v1_funct_2(sK8,k1_relat_1(sK8),X0)
        | ~ v1_funct_1(sK8)
        | v1_xboole_0(X0) )
    | spl10_9
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f2557,f91])).

fof(f2557,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK9))))
        | ~ v1_funct_2(sK9,X0,k2_relat_1(sK9))
        | ~ v1_funct_1(sK9)
        | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0)))
        | ~ v1_funct_2(sK8,k1_relat_1(sK8),X0)
        | ~ v1_funct_1(sK8)
        | v1_xboole_0(X0) )
    | spl10_9
    | ~ spl10_61 ),
    inference(resolution,[],[f1915,f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).

fof(f1915,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))
    | spl10_9
    | ~ spl10_61 ),
    inference(backward_demodulation,[],[f1472,f1846])).

fof(f1472,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | spl10_9 ),
    inference(subsumption_resolution,[],[f1471,f88])).

fof(f1471,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ v1_funct_1(sK8)
    | spl10_9 ),
    inference(subsumption_resolution,[],[f1470,f557])).

fof(f1470,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_9 ),
    inference(subsumption_resolution,[],[f1469,f91])).

fof(f1469,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_9 ),
    inference(subsumption_resolution,[],[f1467,f565])).

fof(f1467,plain,
    ( ~ v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_9 ),
    inference(superposition,[],[f784,f141])).

fof(f784,plain,
    ( ~ v1_funct_2(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))
    | spl10_9 ),
    inference(avatar_component_clause,[],[f782])).

fof(f2456,plain,(
    spl10_68 ),
    inference(avatar_split_clause,[],[f565,f2030])).

fof(f2302,plain,
    ( spl10_73
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f2301,f1844,f2068])).

fof(f2301,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f557,f1846])).

fof(f2254,plain,
    ( spl10_82
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f2246,f1844,f2113])).

fof(f2246,plain,
    ( v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8))
    | ~ spl10_61 ),
    inference(backward_demodulation,[],[f405,f1846])).

fof(f2218,plain,(
    ~ spl10_62 ),
    inference(avatar_contradiction_clause,[],[f2217])).

fof(f2217,plain,
    ( $false
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f2202,f100])).

fof(f100,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2202,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f358,f2197])).

fof(f2197,plain,
    ( k1_xboole_0 = k2_relat_1(sK8)
    | ~ spl10_62 ),
    inference(resolution,[],[f1850,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1850,plain,
    ( sP0(u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f1848])).

fof(f1848,plain,
    ( spl10_62
  <=> sP0(u1_struct_0(sK5),k2_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f2187,plain,
    ( ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f2156,f692,f510,f848,f844,f840,f836,f832])).

fof(f832,plain,
    ( spl10_14
  <=> v1_funct_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f836,plain,
    ( spl10_15
  <=> m1_subset_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK9),k2_relat_1(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f840,plain,
    ( spl10_16
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f844,plain,
    ( spl10_17
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f2156,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK5))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))
    | ~ m1_subset_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK9),k2_relat_1(sK8))))
    | ~ v1_funct_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(superposition,[],[f1201,f141])).

fof(f1201,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k1_partfun1(k2_relat_1(sK9),k2_relat_1(sK8),k2_relat_1(sK8),u1_struct_0(sK5),k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f1046,f512])).

fof(f1046,plain,
    ( ~ r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),k2_relat_1(sK9),sK8,sK9)),k1_partfun1(k2_relat_1(sK9),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8)))
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f99,f693])).

fof(f99,plain,(
    ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK9)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8))) ),
    inference(cnf_transformation,[],[f72])).

fof(f2056,plain,(
    spl10_72 ),
    inference(avatar_split_clause,[],[f409,f2047])).

fof(f2052,plain,(
    spl10_69 ),
    inference(avatar_split_clause,[],[f355,f2034])).

fof(f1851,plain,
    ( spl10_61
    | spl10_62 ),
    inference(avatar_split_clause,[],[f1842,f1848,f1844])).

fof(f1842,plain,
    ( sP0(u1_struct_0(sK5),k2_relat_1(sK8))
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f1808,f405])).

fof(f1808,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | sP0(u1_struct_0(sK5),k2_relat_1(sK8))
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(resolution,[],[f502,f557])).

fof(f502,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f498,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f44,f61,f60,f59])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f498,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f122,f118])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f1304,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f1303])).

fof(f1303,plain,
    ( $false
    | spl10_17 ),
    inference(subsumption_resolution,[],[f1300,f469])).

fof(f469,plain,(
    sP3(u1_struct_0(sK5),k2_relat_1(sK8),sK8) ),
    inference(forward_demodulation,[],[f468,f310])).

fof(f468,plain,(
    sP3(u1_struct_0(sK5),k2_struct_0(sK6),sK8) ),
    inference(subsumption_resolution,[],[f466,f85])).

fof(f466,plain,
    ( sP3(u1_struct_0(sK5),k2_struct_0(sK6),sK8)
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f456,f106])).

fof(f456,plain,(
    sP3(u1_struct_0(sK5),u1_struct_0(sK6),sK8) ),
    inference(subsumption_resolution,[],[f455,f88])).

fof(f455,plain,
    ( sP3(u1_struct_0(sK5),u1_struct_0(sK6),sK8)
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f450,f89])).

fof(f450,plain,
    ( sP3(u1_struct_0(sK5),u1_struct_0(sK6),sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[],[f131,f90])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f46,f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f1300,plain,
    ( ~ sP3(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | spl10_17 ),
    inference(resolution,[],[f846,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f846,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK5))))
    | spl10_17 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1200,plain,(
    spl10_38 ),
    inference(avatar_split_clause,[],[f1037,f1128])).

fof(f1037,plain,(
    k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) ),
    inference(forward_demodulation,[],[f374,f355])).

fof(f374,plain,(
    k1_relat_1(sK9) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) ),
    inference(forward_demodulation,[],[f373,f310])).

fof(f373,plain,(
    k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK8) = k1_relat_1(sK9) ),
    inference(subsumption_resolution,[],[f369,f85])).

fof(f369,plain,
    ( k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK8) = k1_relat_1(sK9)
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f326,f106])).

fof(f326,plain,(
    k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = k1_relat_1(sK9) ),
    inference(backward_demodulation,[],[f94,f286])).

fof(f1081,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f1080])).

fof(f1080,plain,
    ( $false
    | spl10_2 ),
    inference(subsumption_resolution,[],[f1079,f85])).

fof(f1079,plain,
    ( ~ l1_struct_0(sK6)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f1078,f310])).

fof(f1078,plain,
    ( k2_struct_0(sK6) != k2_relat_1(sK8)
    | ~ l1_struct_0(sK6)
    | spl10_2 ),
    inference(superposition,[],[f511,f106])).

fof(f511,plain,
    ( u1_struct_0(sK6) != k2_relat_1(sK8)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f510])).

fof(f889,plain,
    ( ~ spl10_2
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f888])).

fof(f888,plain,
    ( $false
    | ~ spl10_2
    | spl10_16 ),
    inference(subsumption_resolution,[],[f887,f88])).

fof(f887,plain,
    ( ~ v1_funct_1(sK8)
    | ~ spl10_2
    | spl10_16 ),
    inference(subsumption_resolution,[],[f886,f405])).

fof(f886,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ spl10_2
    | spl10_16 ),
    inference(subsumption_resolution,[],[f885,f519])).

fof(f519,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f90,f512])).

fof(f885,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ spl10_2
    | spl10_16 ),
    inference(subsumption_resolution,[],[f884,f535])).

fof(f535,plain,
    ( k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f377,f512])).

fof(f377,plain,(
    k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = k2_relat_1(sK8) ),
    inference(backward_demodulation,[],[f326,f355])).

fof(f884,plain,
    ( k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_16 ),
    inference(subsumption_resolution,[],[f883,f95])).

fof(f883,plain,
    ( ~ v2_funct_1(sK8)
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_16 ),
    inference(subsumption_resolution,[],[f879,f713])).

fof(f713,plain,(
    v1_funct_1(k2_funct_1(sK8)) ),
    inference(resolution,[],[f677,f132])).

fof(f677,plain,(
    sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8) ),
    inference(subsumption_resolution,[],[f676,f88])).

fof(f676,plain,
    ( sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f675,f411])).

fof(f411,plain,(
    v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8)) ),
    inference(subsumption_resolution,[],[f410,f83])).

fof(f410,plain,
    ( v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8))
    | ~ l1_struct_0(sK5) ),
    inference(superposition,[],[f405,f106])).

fof(f675,plain,
    ( sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f674,f95])).

fof(f674,plain,
    ( ~ v2_funct_1(sK8)
    | sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f663,f625])).

fof(f625,plain,(
    k2_relat_1(sK8) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK8),sK8) ),
    inference(forward_demodulation,[],[f341,f355])).

fof(f341,plain,(
    k1_relat_1(sK9) = k2_relset_1(k2_struct_0(sK5),k1_relat_1(sK9),sK8) ),
    inference(backward_demodulation,[],[f215,f286])).

fof(f215,plain,(
    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK8) ),
    inference(subsumption_resolution,[],[f214,f85])).

fof(f214,plain,
    ( k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK8)
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f166,f106])).

fof(f166,plain,(
    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK8) ),
    inference(subsumption_resolution,[],[f152,f83])).

fof(f152,plain,
    ( k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK8)
    | ~ l1_struct_0(sK5) ),
    inference(superposition,[],[f94,f106])).

fof(f663,plain,
    ( k2_relat_1(sK8) != k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ v2_funct_1(sK8)
    | sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[],[f135,f563])).

fof(f879,plain,
    ( ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | spl10_16 ),
    inference(superposition,[],[f842,f136])).

fof(f842,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))
    | spl10_16 ),
    inference(avatar_component_clause,[],[f840])).

fof(f871,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f870])).

fof(f870,plain,
    ( $false
    | spl10_15 ),
    inference(subsumption_resolution,[],[f868,f483])).

fof(f483,plain,(
    sP3(k2_relat_1(sK8),k2_relat_1(sK9),sK9) ),
    inference(forward_demodulation,[],[f482,f311])).

fof(f482,plain,(
    sP3(k2_relat_1(sK8),k2_struct_0(sK7),sK9) ),
    inference(subsumption_resolution,[],[f481,f87])).

fof(f481,plain,
    ( sP3(k2_relat_1(sK8),k2_struct_0(sK7),sK9)
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f473,f106])).

fof(f473,plain,(
    sP3(k2_relat_1(sK8),u1_struct_0(sK7),sK9) ),
    inference(forward_demodulation,[],[f472,f310])).

fof(f472,plain,(
    sP3(k2_struct_0(sK6),u1_struct_0(sK7),sK9) ),
    inference(subsumption_resolution,[],[f470,f85])).

fof(f470,plain,
    ( sP3(k2_struct_0(sK6),u1_struct_0(sK7),sK9)
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f458,f106])).

fof(f458,plain,(
    sP3(u1_struct_0(sK6),u1_struct_0(sK7),sK9) ),
    inference(subsumption_resolution,[],[f457,f91])).

fof(f457,plain,
    ( sP3(u1_struct_0(sK6),u1_struct_0(sK7),sK9)
    | ~ v1_funct_1(sK9) ),
    inference(subsumption_resolution,[],[f451,f92])).

fof(f451,plain,
    ( sP3(u1_struct_0(sK6),u1_struct_0(sK7),sK9)
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v1_funct_1(sK9) ),
    inference(resolution,[],[f131,f93])).

fof(f868,plain,
    ( ~ sP3(k2_relat_1(sK8),k2_relat_1(sK9),sK9)
    | spl10_15 ),
    inference(resolution,[],[f838,f130])).

fof(f838,plain,
    ( ~ m1_subset_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK9),k2_relat_1(sK8))))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f836])).

fof(f859,plain,(
    spl10_14 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | spl10_14 ),
    inference(subsumption_resolution,[],[f856,f483])).

fof(f856,plain,
    ( ~ sP3(k2_relat_1(sK8),k2_relat_1(sK9),sK9)
    | spl10_14 ),
    inference(resolution,[],[f834,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f834,plain,
    ( ~ v1_funct_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9))
    | spl10_14 ),
    inference(avatar_component_clause,[],[f832])).

fof(f813,plain,
    ( ~ spl10_2
    | spl10_8 ),
    inference(avatar_contradiction_clause,[],[f812])).

fof(f812,plain,
    ( $false
    | ~ spl10_2
    | spl10_8 ),
    inference(subsumption_resolution,[],[f811,f88])).

fof(f811,plain,
    ( ~ v1_funct_1(sK8)
    | ~ spl10_2
    | spl10_8 ),
    inference(subsumption_resolution,[],[f810,f519])).

fof(f810,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f809,f91])).

fof(f809,plain,
    ( ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f807,f565])).

fof(f807,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))
    | ~ v1_funct_1(sK8)
    | spl10_8 ),
    inference(resolution,[],[f780,f142])).

fof(f142,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f780,plain,
    ( ~ v1_funct_1(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f778])).

fof(f699,plain,(
    spl10_4 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl10_4 ),
    inference(subsumption_resolution,[],[f697,f87])).

fof(f697,plain,
    ( ~ l1_struct_0(sK7)
    | spl10_4 ),
    inference(subsumption_resolution,[],[f696,f311])).

fof(f696,plain,
    ( k2_struct_0(sK7) != k2_relat_1(sK9)
    | ~ l1_struct_0(sK7)
    | spl10_4 ),
    inference(superposition,[],[f694,f106])).

fof(f694,plain,
    ( u1_struct_0(sK7) != k2_relat_1(sK9)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (4674)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (4682)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (4670)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (4688)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (4671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (4672)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (4678)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (4679)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (4673)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.24/0.52  % (4669)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.52  % (4684)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.24/0.52  % (4689)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.24/0.52  % (4685)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.24/0.53  % (4690)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.24/0.53  % (4691)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.24/0.53  % (4687)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.24/0.53  % (4692)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.24/0.54  % (4668)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.24/0.54  % (4675)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.24/0.54  % (4681)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.54  % (4694)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.45/0.55  % (4676)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.45/0.55  % (4686)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.45/0.56  % (4680)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.45/0.56  % (4693)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.45/0.56  % (4677)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.58/0.70  % (4672)Refutation found. Thanks to Tanya!
% 2.58/0.70  % SZS status Theorem for theBenchmark
% 2.58/0.70  % SZS output start Proof for theBenchmark
% 2.58/0.70  fof(f3689,plain,(
% 2.58/0.70    $false),
% 2.58/0.70    inference(avatar_sat_refutation,[],[f699,f813,f859,f871,f889,f1081,f1200,f1304,f1851,f2052,f2056,f2187,f2218,f2254,f2302,f2456,f3125,f3194,f3232,f3271,f3278,f3332,f3543,f3646,f3654,f3688])).
% 2.58/0.70  fof(f3688,plain,(
% 2.58/0.70    spl10_124 | ~spl10_132),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f3687])).
% 2.58/0.70  fof(f3687,plain,(
% 2.58/0.70    $false | (spl10_124 | ~spl10_132)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3686,f3353])).
% 2.58/0.70  fof(f3353,plain,(
% 2.58/0.70    sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~spl10_132),
% 2.58/0.70    inference(avatar_component_clause,[],[f3351])).
% 2.58/0.70  fof(f3351,plain,(
% 2.58/0.70    spl10_132 <=> sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).
% 2.58/0.70  fof(f3686,plain,(
% 2.58/0.70    ~sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | spl10_124),
% 2.58/0.70    inference(resolution,[],[f3170,f612])).
% 2.58/0.70  fof(f612,plain,(
% 2.58/0.70    ( ! [X4,X5,X3] : (r2_funct_2(X3,X4,k2_funct_1(X5),k2_funct_1(X5)) | ~sP4(X4,X3,X5)) )),
% 2.58/0.70    inference(subsumption_resolution,[],[f611,f132])).
% 2.58/0.70  fof(f132,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | v1_funct_1(k2_funct_1(X2))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f81])).
% 2.58/0.70  fof(f81,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP4(X0,X1,X2))),
% 2.58/0.70    inference(nnf_transformation,[],[f65])).
% 2.58/0.70  fof(f65,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP4(X0,X1,X2))),
% 2.58/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.58/0.70  fof(f611,plain,(
% 2.58/0.70    ( ! [X4,X5,X3] : (r2_funct_2(X3,X4,k2_funct_1(X5),k2_funct_1(X5)) | ~v1_funct_1(k2_funct_1(X5)) | ~sP4(X4,X3,X5)) )),
% 2.58/0.70    inference(subsumption_resolution,[],[f604,f133])).
% 2.58/0.70  fof(f133,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | ~sP4(X0,X1,X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f81])).
% 2.58/0.70  fof(f604,plain,(
% 2.58/0.70    ( ! [X4,X5,X3] : (r2_funct_2(X3,X4,k2_funct_1(X5),k2_funct_1(X5)) | ~v1_funct_2(k2_funct_1(X5),X3,X4) | ~v1_funct_1(k2_funct_1(X5)) | ~sP4(X4,X3,X5)) )),
% 2.58/0.70    inference(resolution,[],[f151,f134])).
% 2.58/0.70  fof(f134,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(X0,X1,X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f81])).
% 2.58/0.70  fof(f151,plain,(
% 2.58/0.70    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.58/0.70    inference(duplicate_literal_removal,[],[f150])).
% 2.58/0.70  fof(f150,plain,(
% 2.58/0.70    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.58/0.70    inference(equality_resolution,[],[f138])).
% 2.58/0.70  fof(f138,plain,(
% 2.58/0.70    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f82])).
% 2.58/0.70  fof(f82,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(nnf_transformation,[],[f52])).
% 2.58/0.70  fof(f52,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(flattening,[],[f51])).
% 2.58/0.70  fof(f51,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.58/0.70    inference(ennf_transformation,[],[f18])).
% 2.58/0.70  fof(f18,axiom,(
% 2.58/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.58/0.70  fof(f3170,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | spl10_124),
% 2.58/0.70    inference(avatar_component_clause,[],[f3168])).
% 2.58/0.70  fof(f3168,plain,(
% 2.58/0.70    spl10_124 <=> r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).
% 2.58/0.70  fof(f3654,plain,(
% 2.58/0.70    spl10_119),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f3653])).
% 2.58/0.70  fof(f3653,plain,(
% 2.58/0.70    $false | spl10_119),
% 2.58/0.70    inference(subsumption_resolution,[],[f3652,f205])).
% 2.58/0.70  fof(f205,plain,(
% 2.58/0.70    v1_relat_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f198,f112])).
% 2.58/0.70  fof(f112,plain,(
% 2.58/0.70    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f4])).
% 2.58/0.70  fof(f4,axiom,(
% 2.58/0.70    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.58/0.70  fof(f198,plain,(
% 2.58/0.70    v1_relat_1(sK8) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))),
% 2.58/0.70    inference(resolution,[],[f108,f90])).
% 2.58/0.70  fof(f90,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f72,plain,(
% 2.58/0.70    ((((~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK9)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8))) & v2_funct_1(sK9) & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) & v2_funct_1(sK8) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK8)) & l1_struct_0(sK7) & ~v2_struct_0(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)) & l1_struct_0(sK5)),
% 2.58/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f27,f71,f70,f69,f68,f67])).
% 2.58/0.70  fof(f67,plain,(
% 2.58/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_struct_0(X2) & ~v2_struct_0(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X3))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_struct_0(X2) & ~v2_struct_0(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK5))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f68,plain,(
% 2.58/0.70    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X3))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_struct_0(X2) & ~v2_struct_0(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3))) & v2_funct_1(X4) & k2_struct_0(X2) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X3)) & l1_struct_0(X2) & ~v2_struct_0(X2)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f69,plain,(
% 2.58/0.70    ? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X2),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3))) & v2_funct_1(X4) & k2_struct_0(X2) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X3)) & l1_struct_0(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),X3,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) & v2_funct_1(X3) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X3)) & l1_struct_0(sK7) & ~v2_struct_0(sK7))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f70,plain,(
% 2.58/0.70    ? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),X3,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X3))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) & v2_funct_1(X3) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) & v2_funct_1(sK8) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X4)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK8))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f71,plain,(
% 2.58/0.70    ? [X4] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,X4)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X4),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) = k2_struct_0(sK7) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X4) & v2_funct_1(sK8) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK9)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8))) & v2_funct_1(sK9) & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) & k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) & v2_funct_1(sK8) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK9))),
% 2.58/0.70    introduced(choice_axiom,[])).
% 2.58/0.70  fof(f27,plain,(
% 2.58/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3))) & v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_struct_0(X2) & ~v2_struct_0(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.58/0.70    inference(flattening,[],[f26])).
% 2.58/0.70  fof(f26,plain,(
% 2.58/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3))) & (v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_struct_0(X2) & ~v2_struct_0(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.58/0.70    inference(ennf_transformation,[],[f25])).
% 2.58/0.70  fof(f25,negated_conjecture,(
% 2.58/0.70    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_struct_0(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3)))))))))),
% 2.58/0.70    inference(negated_conjecture,[],[f24])).
% 2.58/0.70  fof(f24,conjecture,(
% 2.58/0.70    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_struct_0(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) & v2_funct_1(X3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X2),k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X3,X4)),k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X3)))))))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tops_2)).
% 2.58/0.70  fof(f108,plain,(
% 2.58/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f31])).
% 2.58/0.70  fof(f31,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.58/0.70    inference(ennf_transformation,[],[f3])).
% 2.58/0.70  fof(f3,axiom,(
% 2.58/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.58/0.70  fof(f3652,plain,(
% 2.58/0.70    ~v1_relat_1(sK8) | spl10_119),
% 2.58/0.70    inference(subsumption_resolution,[],[f3651,f88])).
% 2.58/0.70  fof(f88,plain,(
% 2.58/0.70    v1_funct_1(sK8)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f3651,plain,(
% 2.58/0.70    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl10_119),
% 2.58/0.70    inference(subsumption_resolution,[],[f3650,f206])).
% 2.58/0.70  fof(f206,plain,(
% 2.58/0.70    v1_relat_1(sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f199,f112])).
% 2.58/0.70  fof(f199,plain,(
% 2.58/0.70    v1_relat_1(sK9) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))),
% 2.58/0.70    inference(resolution,[],[f108,f93])).
% 2.58/0.70  fof(f93,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f3650,plain,(
% 2.58/0.70    ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl10_119),
% 2.58/0.70    inference(subsumption_resolution,[],[f3649,f91])).
% 2.58/0.70  fof(f91,plain,(
% 2.58/0.70    v1_funct_1(sK9)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f3649,plain,(
% 2.58/0.70    ~v1_funct_1(sK9) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl10_119),
% 2.58/0.70    inference(subsumption_resolution,[],[f3648,f95])).
% 2.58/0.70  fof(f95,plain,(
% 2.58/0.70    v2_funct_1(sK8)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f3648,plain,(
% 2.58/0.70    ~v2_funct_1(sK8) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl10_119),
% 2.58/0.70    inference(subsumption_resolution,[],[f3647,f98])).
% 2.58/0.70  fof(f98,plain,(
% 2.58/0.70    v2_funct_1(sK9)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f3647,plain,(
% 2.58/0.70    ~v2_funct_1(sK9) | ~v2_funct_1(sK8) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl10_119),
% 2.58/0.70    inference(resolution,[],[f3142,f110])).
% 2.58/0.70  fof(f110,plain,(
% 2.58/0.70    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f35])).
% 2.58/0.70  fof(f35,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/0.70    inference(flattening,[],[f34])).
% 2.58/0.70  fof(f34,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f10])).
% 2.58/0.70  fof(f10,axiom,(
% 2.58/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 2.58/0.70  fof(f3142,plain,(
% 2.58/0.70    ~v2_funct_1(k5_relat_1(sK8,sK9)) | spl10_119),
% 2.58/0.70    inference(avatar_component_clause,[],[f3140])).
% 2.58/0.70  fof(f3140,plain,(
% 2.58/0.70    spl10_119 <=> v2_funct_1(k5_relat_1(sK8,sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).
% 2.58/0.70  fof(f3646,plain,(
% 2.58/0.70    ~spl10_69 | ~spl10_117 | spl10_118),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f3645])).
% 2.58/0.70  fof(f3645,plain,(
% 2.58/0.70    $false | (~spl10_69 | ~spl10_117 | spl10_118)),
% 2.58/0.70    inference(trivial_inequality_removal,[],[f3644])).
% 2.58/0.70  fof(f3644,plain,(
% 2.58/0.70    k2_relat_1(sK8) != k2_relat_1(sK8) | (~spl10_69 | ~spl10_117 | spl10_118)),
% 2.58/0.70    inference(resolution,[],[f3642,f144])).
% 2.58/0.70  fof(f144,plain,(
% 2.58/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.58/0.70    inference(equality_resolution,[],[f116])).
% 2.58/0.70  fof(f116,plain,(
% 2.58/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.58/0.70    inference(cnf_transformation,[],[f74])).
% 2.58/0.70  fof(f74,plain,(
% 2.58/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.70    inference(flattening,[],[f73])).
% 2.58/0.70  fof(f73,plain,(
% 2.58/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.58/0.70    inference(nnf_transformation,[],[f2])).
% 2.58/0.70  fof(f2,axiom,(
% 2.58/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.58/0.70  fof(f3642,plain,(
% 2.58/0.70    ( ! [X0] : (~r1_tarski(k2_relat_1(sK8),X0) | k2_relat_1(sK8) != X0) ) | (~spl10_69 | ~spl10_117 | spl10_118)),
% 2.58/0.70    inference(forward_demodulation,[],[f3641,f2036])).
% 2.58/0.70  fof(f2036,plain,(
% 2.58/0.70    k1_relat_1(sK9) = k2_relat_1(sK8) | ~spl10_69),
% 2.58/0.70    inference(avatar_component_clause,[],[f2034])).
% 2.58/0.70  fof(f2034,plain,(
% 2.58/0.70    spl10_69 <=> k1_relat_1(sK9) = k2_relat_1(sK8)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).
% 2.58/0.70  fof(f3641,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK8) != X0 | ~r1_tarski(k1_relat_1(sK9),X0)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3640,f206])).
% 2.58/0.70  fof(f3640,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK8) != X0 | ~r1_tarski(k1_relat_1(sK9),X0) | ~v1_relat_1(sK9)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(trivial_inequality_removal,[],[f3638])).
% 2.58/0.70  fof(f3638,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK9) != k2_relat_1(sK9) | k2_relat_1(sK8) != X0 | ~r1_tarski(k1_relat_1(sK9),X0) | ~v1_relat_1(sK9)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(superposition,[],[f3634,f114])).
% 2.58/0.70  fof(f114,plain,(
% 2.58/0.70    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f40])).
% 2.58/0.70  fof(f40,plain,(
% 2.58/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.58/0.70    inference(flattening,[],[f39])).
% 2.58/0.70  fof(f39,plain,(
% 2.58/0.70    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.58/0.70    inference(ennf_transformation,[],[f8])).
% 2.58/0.70  fof(f8,axiom,(
% 2.58/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 2.58/0.70  fof(f3634,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0)) | k2_relat_1(sK8) != X0) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(forward_demodulation,[],[f3633,f105])).
% 2.58/0.70  fof(f105,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.58/0.70    inference(cnf_transformation,[],[f6])).
% 2.58/0.70  fof(f6,axiom,(
% 2.58/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.58/0.70  fof(f3633,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK8)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3632,f206])).
% 2.58/0.70  fof(f3632,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK8) | ~v1_relat_1(sK9)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3625,f101])).
% 2.58/0.70  fof(f101,plain,(
% 2.58/0.70    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f9])).
% 2.58/0.70  fof(f9,axiom,(
% 2.58/0.70    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 2.58/0.70  fof(f3625,plain,(
% 2.58/0.70    ( ! [X0] : (k2_relat_1(sK9) != k2_relat_1(k7_relat_1(sK9,X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK8) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK9)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(superposition,[],[f3588,f113])).
% 2.58/0.70  fof(f113,plain,(
% 2.58/0.70    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f38])).
% 2.58/0.70  fof(f38,plain,(
% 2.58/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.58/0.70    inference(ennf_transformation,[],[f7])).
% 2.58/0.70  fof(f7,axiom,(
% 2.58/0.70    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.58/0.70  fof(f3588,plain,(
% 2.58/0.70    ( ! [X1] : (k2_relat_1(sK9) != k2_relat_1(k5_relat_1(X1,sK9)) | k2_relat_1(X1) != k2_relat_1(sK8) | ~v1_relat_1(X1)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3587,f205])).
% 2.58/0.70  fof(f3587,plain,(
% 2.58/0.70    ( ! [X1] : (k2_relat_1(sK9) != k2_relat_1(k5_relat_1(X1,sK9)) | k2_relat_1(X1) != k2_relat_1(sK8) | ~v1_relat_1(sK8) | ~v1_relat_1(X1)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3585,f206])).
% 2.58/0.70  fof(f3585,plain,(
% 2.58/0.70    ( ! [X1] : (k2_relat_1(sK9) != k2_relat_1(k5_relat_1(X1,sK9)) | k2_relat_1(X1) != k2_relat_1(sK8) | ~v1_relat_1(sK9) | ~v1_relat_1(sK8) | ~v1_relat_1(X1)) ) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(superposition,[],[f3584,f107])).
% 2.58/0.70  fof(f107,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f30])).
% 2.58/0.70  fof(f30,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.58/0.70    inference(flattening,[],[f29])).
% 2.58/0.70  fof(f29,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.58/0.70    inference(ennf_transformation,[],[f5])).
% 2.58/0.70  fof(f5,axiom,(
% 2.58/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 2.58/0.70  fof(f3584,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relat_1(k5_relat_1(sK8,sK9)) | (~spl10_117 | spl10_118)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3583,f3133])).
% 2.58/0.70  fof(f3133,plain,(
% 2.58/0.70    m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | ~spl10_117),
% 2.58/0.70    inference(avatar_component_clause,[],[f3132])).
% 2.58/0.70  fof(f3132,plain,(
% 2.58/0.70    spl10_117 <=> m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_117])])).
% 2.58/0.70  fof(f3583,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relat_1(k5_relat_1(sK8,sK9)) | ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | spl10_118),
% 2.58/0.70    inference(superposition,[],[f3138,f119])).
% 2.58/0.70  fof(f119,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f42])).
% 2.58/0.70  fof(f42,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(ennf_transformation,[],[f13])).
% 2.58/0.70  fof(f13,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.58/0.70  fof(f3138,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | spl10_118),
% 2.58/0.70    inference(avatar_component_clause,[],[f3136])).
% 2.58/0.70  fof(f3136,plain,(
% 2.58/0.70    spl10_118 <=> k2_relat_1(sK9) = k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).
% 2.58/0.70  fof(f3543,plain,(
% 2.58/0.70    spl10_132 | ~spl10_119 | ~spl10_118 | ~spl10_8 | ~spl10_116 | ~spl10_117),
% 2.58/0.70    inference(avatar_split_clause,[],[f3542,f3132,f3128,f778,f3136,f3140,f3351])).
% 2.58/0.70  fof(f778,plain,(
% 2.58/0.70    spl10_8 <=> v1_funct_1(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 2.58/0.70  fof(f3128,plain,(
% 2.58/0.70    spl10_116 <=> v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).
% 2.58/0.70  fof(f3542,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | (~spl10_8 | ~spl10_116 | ~spl10_117)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3541,f855])).
% 2.58/0.70  fof(f855,plain,(
% 2.58/0.70    v1_funct_1(k5_relat_1(sK8,sK9)) | ~spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f854,f88])).
% 2.58/0.70  fof(f854,plain,(
% 2.58/0.70    v1_funct_1(k5_relat_1(sK8,sK9)) | ~v1_funct_1(sK8) | ~spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f853,f563])).
% 2.58/0.70  fof(f563,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8))))),
% 2.58/0.70    inference(forward_demodulation,[],[f339,f355])).
% 2.58/0.70  fof(f355,plain,(
% 2.58/0.70    k1_relat_1(sK9) = k2_relat_1(sK8)),
% 2.58/0.70    inference(backward_demodulation,[],[f286,f310])).
% 2.58/0.70  fof(f310,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relat_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f294,f90])).
% 2.58/0.70  fof(f294,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relat_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 2.58/0.70    inference(superposition,[],[f119,f94])).
% 2.58/0.70  fof(f94,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f286,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k1_relat_1(sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f278,f93])).
% 2.58/0.70  fof(f278,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k1_relat_1(sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 2.58/0.70    inference(superposition,[],[f118,f96])).
% 2.58/0.70  fof(f96,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f118,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f41])).
% 2.58/0.70  fof(f41,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(ennf_transformation,[],[f12])).
% 2.58/0.70  fof(f12,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.58/0.70  fof(f339,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k1_relat_1(sK9))))),
% 2.58/0.70    inference(backward_demodulation,[],[f191,f286])).
% 2.58/0.70  fof(f191,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))),
% 2.58/0.70    inference(subsumption_resolution,[],[f190,f85])).
% 2.58/0.70  fof(f85,plain,(
% 2.58/0.70    l1_struct_0(sK6)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f190,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f167,f106])).
% 2.58/0.70  fof(f106,plain,(
% 2.58/0.70    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f28])).
% 2.58/0.70  fof(f28,plain,(
% 2.58/0.70    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.58/0.70    inference(ennf_transformation,[],[f20])).
% 2.58/0.70  fof(f20,axiom,(
% 2.58/0.70    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.58/0.70  fof(f167,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6))))),
% 2.58/0.70    inference(subsumption_resolution,[],[f153,f83])).
% 2.58/0.70  fof(f83,plain,(
% 2.58/0.70    l1_struct_0(sK5)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f153,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6)))) | ~l1_struct_0(sK5)),
% 2.58/0.70    inference(superposition,[],[f90,f106])).
% 2.58/0.70  fof(f853,plain,(
% 2.58/0.70    v1_funct_1(k5_relat_1(sK8,sK9)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | ~spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f852,f91])).
% 2.58/0.70  fof(f852,plain,(
% 2.58/0.70    v1_funct_1(k5_relat_1(sK8,sK9)) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | ~spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f820,f565])).
% 2.58/0.70  fof(f565,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))),
% 2.58/0.70    inference(forward_demodulation,[],[f564,f355])).
% 2.58/0.70  fof(f564,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),k2_relat_1(sK9))))),
% 2.58/0.70    inference(forward_demodulation,[],[f340,f311])).
% 2.58/0.70  fof(f311,plain,(
% 2.58/0.70    k2_struct_0(sK7) = k2_relat_1(sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f295,f93])).
% 2.58/0.70  fof(f295,plain,(
% 2.58/0.70    k2_struct_0(sK7) = k2_relat_1(sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 2.58/0.70    inference(superposition,[],[f119,f97])).
% 2.58/0.70  fof(f97,plain,(
% 2.58/0.70    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f340,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),k2_struct_0(sK7))))),
% 2.58/0.70    inference(backward_demodulation,[],[f195,f286])).
% 2.58/0.70  fof(f195,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7))))),
% 2.58/0.70    inference(subsumption_resolution,[],[f194,f87])).
% 2.58/0.70  fof(f87,plain,(
% 2.58/0.70    l1_struct_0(sK7)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f194,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) | ~l1_struct_0(sK7)),
% 2.58/0.70    inference(superposition,[],[f172,f106])).
% 2.58/0.70  fof(f172,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK7))))),
% 2.58/0.70    inference(subsumption_resolution,[],[f158,f85])).
% 2.58/0.70  fof(f158,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK7)))) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f93,f106])).
% 2.58/0.70  fof(f820,plain,(
% 2.58/0.70    v1_funct_1(k5_relat_1(sK8,sK9)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | ~spl10_8),
% 2.58/0.70    inference(superposition,[],[f816,f141])).
% 2.58/0.70  fof(f141,plain,(
% 2.58/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f56])).
% 2.58/0.70  fof(f56,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.58/0.70    inference(flattening,[],[f55])).
% 2.58/0.70  fof(f55,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.58/0.70    inference(ennf_transformation,[],[f17])).
% 2.58/0.70  fof(f17,axiom,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.58/0.70  fof(f816,plain,(
% 2.58/0.70    v1_funct_1(k1_partfun1(k2_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)) | ~spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f815,f83])).
% 2.58/0.70  fof(f815,plain,(
% 2.58/0.70    v1_funct_1(k1_partfun1(k2_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)) | ~l1_struct_0(sK5) | ~spl10_8),
% 2.58/0.70    inference(superposition,[],[f779,f106])).
% 2.58/0.70  fof(f779,plain,(
% 2.58/0.70    v1_funct_1(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)) | ~spl10_8),
% 2.58/0.70    inference(avatar_component_clause,[],[f778])).
% 2.58/0.70  fof(f3541,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~v1_funct_1(k5_relat_1(sK8,sK9)) | (~spl10_116 | ~spl10_117)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3532,f3129])).
% 2.58/0.70  fof(f3129,plain,(
% 2.58/0.70    v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~spl10_116),
% 2.58/0.70    inference(avatar_component_clause,[],[f3128])).
% 2.58/0.70  fof(f3532,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | sP4(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(k5_relat_1(sK8,sK9)) | ~spl10_117),
% 2.58/0.70    inference(resolution,[],[f3133,f135])).
% 2.58/0.70  fof(f135,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP4(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f66])).
% 2.58/0.70  fof(f66,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (sP4(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(definition_folding,[],[f48,f65])).
% 2.58/0.70  fof(f48,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(flattening,[],[f47])).
% 2.58/0.70  fof(f47,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.58/0.70    inference(ennf_transformation,[],[f19])).
% 2.58/0.70  fof(f19,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.58/0.70  fof(f3332,plain,(
% 2.58/0.70    spl10_117 | ~spl10_68 | ~spl10_73 | ~spl10_77),
% 2.58/0.70    inference(avatar_split_clause,[],[f3331,f2085,f2068,f2030,f3132])).
% 2.58/0.70  fof(f2030,plain,(
% 2.58/0.70    spl10_68 <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).
% 2.58/0.70  fof(f2068,plain,(
% 2.58/0.70    spl10_73 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).
% 2.58/0.70  fof(f2085,plain,(
% 2.58/0.70    spl10_77 <=> m1_subset_1(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).
% 2.58/0.70  fof(f3331,plain,(
% 2.58/0.70    m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | (~spl10_68 | ~spl10_73 | ~spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3330,f88])).
% 2.58/0.70  fof(f3330,plain,(
% 2.58/0.70    m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_73 | ~spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3329,f2069])).
% 2.58/0.70  fof(f2069,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~spl10_73),
% 2.58/0.70    inference(avatar_component_clause,[],[f2068])).
% 2.58/0.70  fof(f3329,plain,(
% 2.58/0.70    m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3328,f91])).
% 2.58/0.70  fof(f3328,plain,(
% 2.58/0.70    m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3295,f2031])).
% 2.58/0.70  fof(f2031,plain,(
% 2.58/0.70    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~spl10_68),
% 2.58/0.70    inference(avatar_component_clause,[],[f2030])).
% 2.58/0.70  fof(f3295,plain,(
% 2.58/0.70    m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | ~spl10_77),
% 2.58/0.70    inference(superposition,[],[f2086,f141])).
% 2.58/0.70  fof(f2086,plain,(
% 2.58/0.70    m1_subset_1(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | ~spl10_77),
% 2.58/0.70    inference(avatar_component_clause,[],[f2085])).
% 2.58/0.70  fof(f3278,plain,(
% 2.58/0.70    ~spl10_68 | ~spl10_73 | spl10_77),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f3277])).
% 2.58/0.70  fof(f3277,plain,(
% 2.58/0.70    $false | (~spl10_68 | ~spl10_73 | spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3276,f88])).
% 2.58/0.70  fof(f3276,plain,(
% 2.58/0.70    ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_73 | spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3275,f2069])).
% 2.58/0.70  fof(f3275,plain,(
% 2.58/0.70    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | (~spl10_68 | spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3274,f91])).
% 2.58/0.70  fof(f3274,plain,(
% 2.58/0.70    ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | (~spl10_68 | spl10_77)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3272,f2031])).
% 2.58/0.70  fof(f3272,plain,(
% 2.58/0.70    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_77),
% 2.58/0.70    inference(resolution,[],[f2087,f143])).
% 2.58/0.70  fof(f143,plain,(
% 2.58/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f58])).
% 2.58/0.70  fof(f58,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.58/0.70    inference(flattening,[],[f57])).
% 2.58/0.70  fof(f57,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.58/0.70    inference(ennf_transformation,[],[f15])).
% 2.58/0.70  fof(f15,axiom,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.58/0.70  fof(f2087,plain,(
% 2.58/0.70    ~m1_subset_1(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | spl10_77),
% 2.58/0.70    inference(avatar_component_clause,[],[f2085])).
% 2.58/0.70  fof(f3271,plain,(
% 2.58/0.70    spl10_116 | ~spl10_68 | ~spl10_73 | ~spl10_76),
% 2.58/0.70    inference(avatar_split_clause,[],[f3270,f2081,f2068,f2030,f3128])).
% 2.58/0.70  fof(f2081,plain,(
% 2.58/0.70    spl10_76 <=> v1_funct_2(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).
% 2.58/0.70  fof(f3270,plain,(
% 2.58/0.70    v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | (~spl10_68 | ~spl10_73 | ~spl10_76)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3269,f88])).
% 2.58/0.70  fof(f3269,plain,(
% 2.58/0.70    v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_73 | ~spl10_76)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3268,f2069])).
% 2.58/0.70  fof(f3268,plain,(
% 2.58/0.70    v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_76)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3267,f91])).
% 2.58/0.70  fof(f3267,plain,(
% 2.58/0.70    v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | (~spl10_68 | ~spl10_76)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3260,f2031])).
% 2.58/0.70  fof(f3260,plain,(
% 2.58/0.70    v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | ~spl10_76),
% 2.58/0.70    inference(superposition,[],[f2082,f141])).
% 2.58/0.70  fof(f2082,plain,(
% 2.58/0.70    v1_funct_2(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~spl10_76),
% 2.58/0.70    inference(avatar_component_clause,[],[f2081])).
% 2.58/0.70  fof(f3232,plain,(
% 2.58/0.70    spl10_76 | ~spl10_9 | ~spl10_61),
% 2.58/0.70    inference(avatar_split_clause,[],[f3229,f1844,f782,f2081])).
% 2.58/0.70  fof(f782,plain,(
% 2.58/0.70    spl10_9 <=> v1_funct_2(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.58/0.70  fof(f1844,plain,(
% 2.58/0.70    spl10_61 <=> u1_struct_0(sK5) = k1_relat_1(sK8)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).
% 2.58/0.70  fof(f3229,plain,(
% 2.58/0.70    v1_funct_2(k1_partfun1(k1_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | (~spl10_9 | ~spl10_61)),
% 2.58/0.70    inference(forward_demodulation,[],[f783,f1846])).
% 2.58/0.70  fof(f1846,plain,(
% 2.58/0.70    u1_struct_0(sK5) = k1_relat_1(sK8) | ~spl10_61),
% 2.58/0.70    inference(avatar_component_clause,[],[f1844])).
% 2.58/0.70  fof(f783,plain,(
% 2.58/0.70    v1_funct_2(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | ~spl10_9),
% 2.58/0.70    inference(avatar_component_clause,[],[f782])).
% 2.58/0.70  fof(f3194,plain,(
% 2.58/0.70    ~spl10_119 | ~spl10_124 | ~spl10_118 | ~spl10_117 | ~spl10_116 | ~spl10_2 | ~spl10_4 | ~spl10_8 | spl10_18 | ~spl10_38 | ~spl10_61),
% 2.58/0.70    inference(avatar_split_clause,[],[f3193,f1844,f1128,f848,f778,f692,f510,f3128,f3132,f3136,f3168,f3140])).
% 2.58/0.70  fof(f510,plain,(
% 2.58/0.70    spl10_2 <=> u1_struct_0(sK6) = k2_relat_1(sK8)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.58/0.70  fof(f692,plain,(
% 2.58/0.70    spl10_4 <=> u1_struct_0(sK7) = k2_relat_1(sK9)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.58/0.70  fof(f848,plain,(
% 2.58/0.70    spl10_18 <=> r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 2.58/0.70  fof(f1128,plain,(
% 2.58/0.70    spl10_38 <=> k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 2.58/0.70  fof(f3193,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | (~spl10_2 | ~spl10_4 | ~spl10_8 | spl10_18 | ~spl10_38 | ~spl10_61)),
% 2.58/0.70    inference(forward_demodulation,[],[f3192,f1846])).
% 2.58/0.70  fof(f3192,plain,(
% 2.58/0.70    ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK9)))) | k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | (~spl10_2 | ~spl10_4 | ~spl10_8 | spl10_18 | ~spl10_38 | ~spl10_61)),
% 2.58/0.70    inference(forward_demodulation,[],[f3191,f1846])).
% 2.58/0.70  fof(f3191,plain,(
% 2.58/0.70    k2_relat_1(sK9) != k2_relset_1(k1_relat_1(sK8),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9)))) | ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | (~spl10_2 | ~spl10_4 | ~spl10_8 | spl10_18 | ~spl10_38 | ~spl10_61)),
% 2.58/0.70    inference(forward_demodulation,[],[f3190,f1846])).
% 2.58/0.70  fof(f3190,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),k1_relat_1(sK8),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | k2_relat_1(sK9) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9)))) | ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | (~spl10_2 | ~spl10_4 | ~spl10_8 | spl10_18 | ~spl10_38 | ~spl10_61)),
% 2.58/0.70    inference(forward_demodulation,[],[f3189,f1846])).
% 2.58/0.70  fof(f3189,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | k2_relat_1(sK9) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9)))) | ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | (~spl10_2 | ~spl10_4 | ~spl10_8 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1799,f855])).
% 2.58/0.70  fof(f1799,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_funct_1(k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(k5_relat_1(sK8,sK9)) | k2_relat_1(sK9) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)) | ~m1_subset_1(k5_relat_1(sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK9)))) | ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | ~v1_funct_1(k5_relat_1(sK8,sK9)) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(superposition,[],[f1797,f136])).
% 2.58/0.70  fof(f136,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f50])).
% 2.58/0.70  fof(f50,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(flattening,[],[f49])).
% 2.58/0.70  fof(f49,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.58/0.70    inference(ennf_transformation,[],[f22])).
% 2.58/0.70  fof(f22,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 2.58/0.70  fof(f1797,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1796,f205])).
% 2.58/0.70  fof(f1796,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v1_relat_1(sK8) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1795,f88])).
% 2.58/0.70  fof(f1795,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1794,f206])).
% 2.58/0.70  fof(f1794,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1793,f91])).
% 2.58/0.70  fof(f1793,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1792,f95])).
% 2.58/0.70  fof(f1792,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(sK8) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1790,f98])).
% 2.58/0.70  fof(f1790,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k2_funct_1(k5_relat_1(sK8,sK9))) | ~v2_funct_1(sK9) | ~v2_funct_1(sK8) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(superposition,[],[f1787,f111])).
% 2.58/0.70  fof(f111,plain,(
% 2.58/0.70    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f37])).
% 2.58/0.70  fof(f37,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.58/0.70    inference(flattening,[],[f36])).
% 2.58/0.70  fof(f36,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f11])).
% 2.58/0.70  fof(f11,axiom,(
% 2.58/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 2.58/0.70  fof(f1787,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8))) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1786,f91])).
% 2.58/0.70  fof(f1786,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8))) | ~v1_funct_1(sK9) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1785,f409])).
% 2.58/0.70  fof(f409,plain,(
% 2.58/0.70    v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))),
% 2.58/0.70    inference(forward_demodulation,[],[f408,f310])).
% 2.58/0.70  fof(f408,plain,(
% 2.58/0.70    v1_funct_2(sK9,k2_struct_0(sK6),k2_relat_1(sK9))),
% 2.58/0.70    inference(subsumption_resolution,[],[f407,f85])).
% 2.58/0.70  fof(f407,plain,(
% 2.58/0.70    v1_funct_2(sK9,k2_struct_0(sK6),k2_relat_1(sK9)) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f362,f106])).
% 2.58/0.70  fof(f362,plain,(
% 2.58/0.70    v1_funct_2(sK9,u1_struct_0(sK6),k2_relat_1(sK9))),
% 2.58/0.70    inference(backward_demodulation,[],[f179,f311])).
% 2.58/0.70  fof(f179,plain,(
% 2.58/0.70    v1_funct_2(sK9,u1_struct_0(sK6),k2_struct_0(sK7))),
% 2.58/0.70    inference(subsumption_resolution,[],[f165,f87])).
% 2.58/0.70  fof(f165,plain,(
% 2.58/0.70    v1_funct_2(sK9,u1_struct_0(sK6),k2_struct_0(sK7)) | ~l1_struct_0(sK7)),
% 2.58/0.70    inference(superposition,[],[f92,f106])).
% 2.58/0.70  fof(f92,plain,(
% 2.58/0.70    v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f1785,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8))) | ~v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(sK9) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1784,f565])).
% 2.58/0.70  fof(f1784,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8))) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(sK9) | (~spl10_2 | ~spl10_4 | spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1783,f1168])).
% 2.58/0.70  fof(f1168,plain,(
% 2.58/0.70    k2_relat_1(sK9) = k2_relset_1(k2_relat_1(sK8),k2_relat_1(sK9),sK9) | (~spl10_2 | ~spl10_4)),
% 2.58/0.70    inference(forward_demodulation,[],[f1043,f512])).
% 2.58/0.70  fof(f512,plain,(
% 2.58/0.70    u1_struct_0(sK6) = k2_relat_1(sK8) | ~spl10_2),
% 2.58/0.70    inference(avatar_component_clause,[],[f510])).
% 2.58/0.70  fof(f1043,plain,(
% 2.58/0.70    k2_relat_1(sK9) = k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK9),sK9) | ~spl10_4),
% 2.58/0.70    inference(forward_demodulation,[],[f359,f693])).
% 2.58/0.70  fof(f693,plain,(
% 2.58/0.70    u1_struct_0(sK7) = k2_relat_1(sK9) | ~spl10_4),
% 2.58/0.70    inference(avatar_component_clause,[],[f692])).
% 2.58/0.70  fof(f359,plain,(
% 2.58/0.70    k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) = k2_relat_1(sK9)),
% 2.58/0.70    inference(backward_demodulation,[],[f97,f311])).
% 2.58/0.70  fof(f1783,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8))) | k2_relat_1(sK9) != k2_relset_1(k2_relat_1(sK8),k2_relat_1(sK9),sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(sK9) | (spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1781,f98])).
% 2.58/0.70  fof(f1781,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_funct_1(sK9),k2_funct_1(sK8))) | ~v2_funct_1(sK9) | k2_relat_1(sK9) != k2_relset_1(k2_relat_1(sK8),k2_relat_1(sK9),sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) | ~v1_funct_1(sK9) | (spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(superposition,[],[f1778,f136])).
% 2.58/0.70  fof(f1778,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8))) | (spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1777,f88])).
% 2.58/0.70  fof(f1777,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8))) | ~v1_funct_1(sK8) | (spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1776,f405])).
% 2.58/0.70  fof(f405,plain,(
% 2.58/0.70    v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8))),
% 2.58/0.70    inference(forward_demodulation,[],[f329,f355])).
% 2.58/0.70  fof(f329,plain,(
% 2.58/0.70    v1_funct_2(sK8,u1_struct_0(sK5),k1_relat_1(sK9))),
% 2.58/0.70    inference(backward_demodulation,[],[f169,f286])).
% 2.58/0.70  fof(f169,plain,(
% 2.58/0.70    v1_funct_2(sK8,u1_struct_0(sK5),k2_struct_0(sK6))),
% 2.58/0.70    inference(subsumption_resolution,[],[f155,f85])).
% 2.58/0.70  fof(f155,plain,(
% 2.58/0.70    v1_funct_2(sK8,u1_struct_0(sK5),k2_struct_0(sK6)) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f89,f106])).
% 2.58/0.70  fof(f89,plain,(
% 2.58/0.70    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f1776,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | (spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1775,f557])).
% 2.58/0.70  fof(f557,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8))))),
% 2.58/0.70    inference(forward_demodulation,[],[f330,f355])).
% 2.58/0.70  fof(f330,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK9))))),
% 2.58/0.70    inference(backward_demodulation,[],[f170,f286])).
% 2.58/0.70  fof(f170,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))),
% 2.58/0.70    inference(subsumption_resolution,[],[f156,f85])).
% 2.58/0.70  fof(f156,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f90,f106])).
% 2.58/0.70  fof(f1775,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | (spl10_18 | ~spl10_38)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1774,f1129])).
% 2.58/0.70  fof(f1129,plain,(
% 2.58/0.70    k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~spl10_38),
% 2.58/0.70    inference(avatar_component_clause,[],[f1128])).
% 2.58/0.70  fof(f1774,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8))) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | spl10_18),
% 2.58/0.70    inference(subsumption_resolution,[],[f1767,f95])).
% 2.58/0.70  fof(f1767,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_funct_1(sK8))) | ~v2_funct_1(sK8) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | spl10_18),
% 2.58/0.70    inference(superposition,[],[f1443,f136])).
% 2.58/0.70  fof(f1443,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | spl10_18),
% 2.58/0.70    inference(subsumption_resolution,[],[f1442,f88])).
% 2.58/0.70  fof(f1442,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | ~v1_funct_1(sK8) | spl10_18),
% 2.58/0.70    inference(subsumption_resolution,[],[f1441,f557])).
% 2.58/0.70  fof(f1441,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_18),
% 2.58/0.70    inference(subsumption_resolution,[],[f1440,f91])).
% 2.58/0.70  fof(f1440,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_18),
% 2.58/0.70    inference(subsumption_resolution,[],[f1435,f565])).
% 2.58/0.70  fof(f1435,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k5_relat_1(sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_18),
% 2.58/0.70    inference(superposition,[],[f850,f141])).
% 2.58/0.70  fof(f850,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | spl10_18),
% 2.58/0.70    inference(avatar_component_clause,[],[f848])).
% 2.58/0.70  fof(f3125,plain,(
% 2.58/0.70    spl10_9 | ~spl10_61 | ~spl10_68 | ~spl10_72 | ~spl10_73 | ~spl10_82),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f3124])).
% 2.58/0.70  fof(f3124,plain,(
% 2.58/0.70    $false | (spl10_9 | ~spl10_61 | ~spl10_68 | ~spl10_72 | ~spl10_73 | ~spl10_82)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3123,f358])).
% 2.58/0.70  fof(f358,plain,(
% 2.58/0.70    ~v1_xboole_0(k2_relat_1(sK8))),
% 2.58/0.70    inference(subsumption_resolution,[],[f357,f84])).
% 2.58/0.70  fof(f84,plain,(
% 2.58/0.70    ~v2_struct_0(sK6)),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f357,plain,(
% 2.58/0.70    ~v1_xboole_0(k2_relat_1(sK8)) | v2_struct_0(sK6)),
% 2.58/0.70    inference(subsumption_resolution,[],[f356,f85])).
% 2.58/0.70  fof(f356,plain,(
% 2.58/0.70    ~v1_xboole_0(k2_relat_1(sK8)) | ~l1_struct_0(sK6) | v2_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f183,f310])).
% 2.58/0.70  fof(f183,plain,(
% 2.58/0.70    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.58/0.70    inference(duplicate_literal_removal,[],[f182])).
% 2.58/0.70  fof(f182,plain,(
% 2.58/0.70    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.58/0.70    inference(superposition,[],[f109,f106])).
% 2.58/0.70  fof(f109,plain,(
% 2.58/0.70    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f33])).
% 2.58/0.70  fof(f33,plain,(
% 2.58/0.70    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.58/0.70    inference(flattening,[],[f32])).
% 2.58/0.70  fof(f32,plain,(
% 2.58/0.70    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f21])).
% 2.58/0.70  fof(f21,axiom,(
% 2.58/0.70    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.58/0.70  fof(f3123,plain,(
% 2.58/0.70    v1_xboole_0(k2_relat_1(sK8)) | (spl10_9 | ~spl10_61 | ~spl10_68 | ~spl10_72 | ~spl10_73 | ~spl10_82)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3122,f2114])).
% 2.58/0.70  fof(f2114,plain,(
% 2.58/0.70    v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8)) | ~spl10_82),
% 2.58/0.70    inference(avatar_component_clause,[],[f2113])).
% 2.58/0.70  fof(f2113,plain,(
% 2.58/0.70    spl10_82 <=> v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).
% 2.58/0.70  fof(f3122,plain,(
% 2.58/0.70    ~v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8)) | v1_xboole_0(k2_relat_1(sK8)) | (spl10_9 | ~spl10_61 | ~spl10_68 | ~spl10_72 | ~spl10_73)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3121,f2069])).
% 2.58/0.70  fof(f3121,plain,(
% 2.58/0.70    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8)) | v1_xboole_0(k2_relat_1(sK8)) | (spl10_9 | ~spl10_61 | ~spl10_68 | ~spl10_72)),
% 2.58/0.70    inference(subsumption_resolution,[],[f3120,f2049])).
% 2.58/0.70  fof(f2049,plain,(
% 2.58/0.70    v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) | ~spl10_72),
% 2.58/0.70    inference(avatar_component_clause,[],[f2047])).
% 2.58/0.70  fof(f2047,plain,(
% 2.58/0.70    spl10_72 <=> v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).
% 2.58/0.70  fof(f3120,plain,(
% 2.58/0.70    ~v1_funct_2(sK9,k2_relat_1(sK8),k2_relat_1(sK9)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8)) | v1_xboole_0(k2_relat_1(sK8)) | (spl10_9 | ~spl10_61 | ~spl10_68)),
% 2.58/0.70    inference(resolution,[],[f2559,f2031])).
% 2.58/0.70  fof(f2559,plain,(
% 2.58/0.70    ( ! [X0] : (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK9)))) | ~v1_funct_2(sK9,X0,k2_relat_1(sK9)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0))) | ~v1_funct_2(sK8,k1_relat_1(sK8),X0) | v1_xboole_0(X0)) ) | (spl10_9 | ~spl10_61)),
% 2.58/0.70    inference(subsumption_resolution,[],[f2558,f88])).
% 2.58/0.70  fof(f2558,plain,(
% 2.58/0.70    ( ! [X0] : (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK9)))) | ~v1_funct_2(sK9,X0,k2_relat_1(sK9)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0))) | ~v1_funct_2(sK8,k1_relat_1(sK8),X0) | ~v1_funct_1(sK8) | v1_xboole_0(X0)) ) | (spl10_9 | ~spl10_61)),
% 2.58/0.70    inference(subsumption_resolution,[],[f2557,f91])).
% 2.58/0.70  fof(f2557,plain,(
% 2.58/0.70    ( ! [X0] : (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK9)))) | ~v1_funct_2(sK9,X0,k2_relat_1(sK9)) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0))) | ~v1_funct_2(sK8,k1_relat_1(sK8),X0) | ~v1_funct_1(sK8) | v1_xboole_0(X0)) ) | (spl10_9 | ~spl10_61)),
% 2.58/0.70    inference(resolution,[],[f1915,f140])).
% 2.58/0.70  fof(f140,plain,(
% 2.58/0.70    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k5_relat_1(X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | v1_xboole_0(X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f54])).
% 2.58/0.70  fof(f54,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4] : ((v1_funct_2(k5_relat_1(X3,X4),X0,X2) & v1_funct_1(k5_relat_1(X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | v1_xboole_0(X1))),
% 2.58/0.70    inference(flattening,[],[f53])).
% 2.58/0.70  fof(f53,plain,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4] : ((v1_funct_2(k5_relat_1(X3,X4),X0,X2) & v1_funct_1(k5_relat_1(X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | v1_xboole_0(X1)))),
% 2.58/0.70    inference(ennf_transformation,[],[f16])).
% 2.58/0.70  fof(f16,axiom,(
% 2.58/0.70    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & ~v1_xboole_0(X1)) => (v1_funct_2(k5_relat_1(X3,X4),X0,X2) & v1_funct_1(k5_relat_1(X3,X4))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).
% 2.58/0.70  fof(f1915,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),k1_relat_1(sK8),k2_relat_1(sK9)) | (spl10_9 | ~spl10_61)),
% 2.58/0.70    inference(backward_demodulation,[],[f1472,f1846])).
% 2.58/0.70  fof(f1472,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | spl10_9),
% 2.58/0.70    inference(subsumption_resolution,[],[f1471,f88])).
% 2.58/0.70  fof(f1471,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | ~v1_funct_1(sK8) | spl10_9),
% 2.58/0.70    inference(subsumption_resolution,[],[f1470,f557])).
% 2.58/0.70  fof(f1470,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_9),
% 2.58/0.70    inference(subsumption_resolution,[],[f1469,f91])).
% 2.58/0.70  fof(f1469,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_9),
% 2.58/0.70    inference(subsumption_resolution,[],[f1467,f565])).
% 2.58/0.70  fof(f1467,plain,(
% 2.58/0.70    ~v1_funct_2(k5_relat_1(sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_9),
% 2.58/0.70    inference(superposition,[],[f784,f141])).
% 2.58/0.70  fof(f784,plain,(
% 2.58/0.70    ~v1_funct_2(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9),u1_struct_0(sK5),k2_relat_1(sK9)) | spl10_9),
% 2.58/0.70    inference(avatar_component_clause,[],[f782])).
% 2.58/0.70  fof(f2456,plain,(
% 2.58/0.70    spl10_68),
% 2.58/0.70    inference(avatar_split_clause,[],[f565,f2030])).
% 2.58/0.70  fof(f2302,plain,(
% 2.58/0.70    spl10_73 | ~spl10_61),
% 2.58/0.70    inference(avatar_split_clause,[],[f2301,f1844,f2068])).
% 2.58/0.70  fof(f2301,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),k2_relat_1(sK8)))) | ~spl10_61),
% 2.58/0.70    inference(forward_demodulation,[],[f557,f1846])).
% 2.58/0.70  fof(f2254,plain,(
% 2.58/0.70    spl10_82 | ~spl10_61),
% 2.58/0.70    inference(avatar_split_clause,[],[f2246,f1844,f2113])).
% 2.58/0.70  fof(f2246,plain,(
% 2.58/0.70    v1_funct_2(sK8,k1_relat_1(sK8),k2_relat_1(sK8)) | ~spl10_61),
% 2.58/0.70    inference(backward_demodulation,[],[f405,f1846])).
% 2.58/0.70  fof(f2218,plain,(
% 2.58/0.70    ~spl10_62),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f2217])).
% 2.58/0.70  fof(f2217,plain,(
% 2.58/0.70    $false | ~spl10_62),
% 2.58/0.70    inference(subsumption_resolution,[],[f2202,f100])).
% 2.58/0.70  fof(f100,plain,(
% 2.58/0.70    v1_xboole_0(k1_xboole_0)),
% 2.58/0.70    inference(cnf_transformation,[],[f1])).
% 2.58/0.70  fof(f1,axiom,(
% 2.58/0.70    v1_xboole_0(k1_xboole_0)),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.58/0.70  fof(f2202,plain,(
% 2.58/0.70    ~v1_xboole_0(k1_xboole_0) | ~spl10_62),
% 2.58/0.70    inference(backward_demodulation,[],[f358,f2197])).
% 2.58/0.70  fof(f2197,plain,(
% 2.58/0.70    k1_xboole_0 = k2_relat_1(sK8) | ~spl10_62),
% 2.58/0.70    inference(resolution,[],[f1850,f124])).
% 2.58/0.70  fof(f124,plain,(
% 2.58/0.70    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 2.58/0.70    inference(cnf_transformation,[],[f79])).
% 2.58/0.70  fof(f79,plain,(
% 2.58/0.70    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 2.58/0.70    inference(nnf_transformation,[],[f59])).
% 2.58/0.70  fof(f59,plain,(
% 2.58/0.70    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 2.58/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.58/0.70  fof(f1850,plain,(
% 2.58/0.70    sP0(u1_struct_0(sK5),k2_relat_1(sK8)) | ~spl10_62),
% 2.58/0.70    inference(avatar_component_clause,[],[f1848])).
% 2.58/0.70  fof(f1848,plain,(
% 2.58/0.70    spl10_62 <=> sP0(u1_struct_0(sK5),k2_relat_1(sK8))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 2.58/0.70  fof(f2187,plain,(
% 2.58/0.70    ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_2 | ~spl10_4),
% 2.58/0.70    inference(avatar_split_clause,[],[f2156,f692,f510,f848,f844,f840,f836,f832])).
% 2.58/0.70  fof(f832,plain,(
% 2.58/0.70    spl10_14 <=> v1_funct_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 2.58/0.70  fof(f836,plain,(
% 2.58/0.70    spl10_15 <=> m1_subset_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK9),k2_relat_1(sK8))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 2.58/0.70  fof(f840,plain,(
% 2.58/0.70    spl10_16 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 2.58/0.70  fof(f844,plain,(
% 2.58/0.70    spl10_17 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK5))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 2.58/0.70  fof(f2156,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k5_relat_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK5)))) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)) | ~m1_subset_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK9),k2_relat_1(sK8)))) | ~v1_funct_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9)) | (~spl10_2 | ~spl10_4)),
% 2.58/0.70    inference(superposition,[],[f1201,f141])).
% 2.58/0.70  fof(f1201,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)),k1_partfun1(k2_relat_1(sK9),k2_relat_1(sK8),k2_relat_1(sK8),u1_struct_0(sK5),k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8))) | (~spl10_2 | ~spl10_4)),
% 2.58/0.70    inference(forward_demodulation,[],[f1046,f512])).
% 2.58/0.70  fof(f1046,plain,(
% 2.58/0.70    ~r2_funct_2(k2_relat_1(sK9),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK9),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),k2_relat_1(sK9),sK8,sK9)),k1_partfun1(k2_relat_1(sK9),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK9),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8))) | ~spl10_4),
% 2.58/0.70    inference(forward_demodulation,[],[f99,f693])).
% 2.58/0.70  fof(f99,plain,(
% 2.58/0.70    ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK7),k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK9)),k1_partfun1(u1_struct_0(sK7),u1_struct_0(sK6),u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK9),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK8)))),
% 2.58/0.70    inference(cnf_transformation,[],[f72])).
% 2.58/0.70  fof(f2056,plain,(
% 2.58/0.70    spl10_72),
% 2.58/0.70    inference(avatar_split_clause,[],[f409,f2047])).
% 2.58/0.70  fof(f2052,plain,(
% 2.58/0.70    spl10_69),
% 2.58/0.70    inference(avatar_split_clause,[],[f355,f2034])).
% 2.58/0.70  fof(f1851,plain,(
% 2.58/0.70    spl10_61 | spl10_62),
% 2.58/0.70    inference(avatar_split_clause,[],[f1842,f1848,f1844])).
% 2.58/0.70  fof(f1842,plain,(
% 2.58/0.70    sP0(u1_struct_0(sK5),k2_relat_1(sK8)) | u1_struct_0(sK5) = k1_relat_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f1808,f405])).
% 2.58/0.70  fof(f1808,plain,(
% 2.58/0.70    ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | sP0(u1_struct_0(sK5),k2_relat_1(sK8)) | u1_struct_0(sK5) = k1_relat_1(sK8)),
% 2.58/0.70    inference(resolution,[],[f502,f557])).
% 2.58/0.70  fof(f502,plain,(
% 2.58/0.70    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 2.58/0.70    inference(subsumption_resolution,[],[f498,f126])).
% 2.58/0.70  fof(f126,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f62])).
% 2.58/0.70  fof(f62,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(definition_folding,[],[f44,f61,f60,f59])).
% 2.58/0.70  fof(f60,plain,(
% 2.58/0.70    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 2.58/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.58/0.70  fof(f61,plain,(
% 2.58/0.70    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 2.58/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.58/0.70  fof(f44,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(flattening,[],[f43])).
% 2.58/0.70  fof(f43,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/0.70    inference(ennf_transformation,[],[f14])).
% 2.58/0.70  fof(f14,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.58/0.70  fof(f498,plain,(
% 2.58/0.70    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.58/0.70    inference(superposition,[],[f122,f118])).
% 2.58/0.70  fof(f122,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f78])).
% 2.58/0.70  fof(f78,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 2.58/0.70    inference(rectify,[],[f77])).
% 2.58/0.70  fof(f77,plain,(
% 2.58/0.70    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 2.58/0.70    inference(nnf_transformation,[],[f60])).
% 2.58/0.70  fof(f1304,plain,(
% 2.58/0.70    spl10_17),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f1303])).
% 2.58/0.70  fof(f1303,plain,(
% 2.58/0.70    $false | spl10_17),
% 2.58/0.70    inference(subsumption_resolution,[],[f1300,f469])).
% 2.58/0.70  fof(f469,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK5),k2_relat_1(sK8),sK8)),
% 2.58/0.70    inference(forward_demodulation,[],[f468,f310])).
% 2.58/0.70  fof(f468,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK5),k2_struct_0(sK6),sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f466,f85])).
% 2.58/0.70  fof(f466,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK5),k2_struct_0(sK6),sK8) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f456,f106])).
% 2.58/0.70  fof(f456,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK5),u1_struct_0(sK6),sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f455,f88])).
% 2.58/0.70  fof(f455,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK5),u1_struct_0(sK6),sK8) | ~v1_funct_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f450,f89])).
% 2.58/0.70  fof(f450,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK5),u1_struct_0(sK6),sK8) | ~v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(sK8)),
% 2.58/0.70    inference(resolution,[],[f131,f90])).
% 2.58/0.70  fof(f131,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f64])).
% 2.58/0.70  fof(f64,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (sP3(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(definition_folding,[],[f46,f63])).
% 2.58/0.70  fof(f63,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP3(X0,X1,X2))),
% 2.58/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.58/0.70  fof(f46,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.58/0.70    inference(flattening,[],[f45])).
% 2.58/0.70  fof(f45,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.58/0.70    inference(ennf_transformation,[],[f23])).
% 2.58/0.70  fof(f23,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 2.58/0.70  fof(f1300,plain,(
% 2.58/0.70    ~sP3(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | spl10_17),
% 2.58/0.70    inference(resolution,[],[f846,f130])).
% 2.58/0.70  fof(f130,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP3(X0,X1,X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f80])).
% 2.58/0.70  fof(f80,plain,(
% 2.58/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP3(X0,X1,X2))),
% 2.58/0.70    inference(nnf_transformation,[],[f63])).
% 2.58/0.70  fof(f846,plain,(
% 2.58/0.70    ~m1_subset_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK5)))) | spl10_17),
% 2.58/0.70    inference(avatar_component_clause,[],[f844])).
% 2.58/0.70  fof(f1200,plain,(
% 2.58/0.70    spl10_38),
% 2.58/0.70    inference(avatar_split_clause,[],[f1037,f1128])).
% 2.58/0.70  fof(f1037,plain,(
% 2.58/0.70    k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)),
% 2.58/0.70    inference(forward_demodulation,[],[f374,f355])).
% 2.58/0.70  fof(f374,plain,(
% 2.58/0.70    k1_relat_1(sK9) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8)),
% 2.58/0.70    inference(forward_demodulation,[],[f373,f310])).
% 2.58/0.70  fof(f373,plain,(
% 2.58/0.70    k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK8) = k1_relat_1(sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f369,f85])).
% 2.58/0.70  fof(f369,plain,(
% 2.58/0.70    k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK8) = k1_relat_1(sK9) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f326,f106])).
% 2.58/0.70  fof(f326,plain,(
% 2.58/0.70    k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = k1_relat_1(sK9)),
% 2.58/0.70    inference(backward_demodulation,[],[f94,f286])).
% 2.58/0.70  fof(f1081,plain,(
% 2.58/0.70    spl10_2),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f1080])).
% 2.58/0.70  fof(f1080,plain,(
% 2.58/0.70    $false | spl10_2),
% 2.58/0.70    inference(subsumption_resolution,[],[f1079,f85])).
% 2.58/0.70  fof(f1079,plain,(
% 2.58/0.70    ~l1_struct_0(sK6) | spl10_2),
% 2.58/0.70    inference(subsumption_resolution,[],[f1078,f310])).
% 2.58/0.70  fof(f1078,plain,(
% 2.58/0.70    k2_struct_0(sK6) != k2_relat_1(sK8) | ~l1_struct_0(sK6) | spl10_2),
% 2.58/0.70    inference(superposition,[],[f511,f106])).
% 2.58/0.70  fof(f511,plain,(
% 2.58/0.70    u1_struct_0(sK6) != k2_relat_1(sK8) | spl10_2),
% 2.58/0.70    inference(avatar_component_clause,[],[f510])).
% 2.58/0.70  fof(f889,plain,(
% 2.58/0.70    ~spl10_2 | spl10_16),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f888])).
% 2.58/0.70  fof(f888,plain,(
% 2.58/0.70    $false | (~spl10_2 | spl10_16)),
% 2.58/0.70    inference(subsumption_resolution,[],[f887,f88])).
% 2.58/0.70  fof(f887,plain,(
% 2.58/0.70    ~v1_funct_1(sK8) | (~spl10_2 | spl10_16)),
% 2.58/0.70    inference(subsumption_resolution,[],[f886,f405])).
% 2.58/0.70  fof(f886,plain,(
% 2.58/0.70    ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | (~spl10_2 | spl10_16)),
% 2.58/0.70    inference(subsumption_resolution,[],[f885,f519])).
% 2.58/0.70  fof(f519,plain,(
% 2.58/0.70    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~spl10_2),
% 2.58/0.70    inference(backward_demodulation,[],[f90,f512])).
% 2.58/0.70  fof(f885,plain,(
% 2.58/0.70    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | (~spl10_2 | spl10_16)),
% 2.58/0.70    inference(subsumption_resolution,[],[f884,f535])).
% 2.58/0.70  fof(f535,plain,(
% 2.58/0.70    k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~spl10_2),
% 2.58/0.70    inference(backward_demodulation,[],[f377,f512])).
% 2.58/0.70  fof(f377,plain,(
% 2.58/0.70    k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = k2_relat_1(sK8)),
% 2.58/0.70    inference(backward_demodulation,[],[f326,f355])).
% 2.58/0.70  fof(f884,plain,(
% 2.58/0.70    k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | spl10_16),
% 2.58/0.70    inference(subsumption_resolution,[],[f883,f95])).
% 2.58/0.70  fof(f883,plain,(
% 2.58/0.70    ~v2_funct_1(sK8) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | spl10_16),
% 2.58/0.70    inference(subsumption_resolution,[],[f879,f713])).
% 2.58/0.70  fof(f713,plain,(
% 2.58/0.70    v1_funct_1(k2_funct_1(sK8))),
% 2.58/0.70    inference(resolution,[],[f677,f132])).
% 2.58/0.70  fof(f677,plain,(
% 2.58/0.70    sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f676,f88])).
% 2.58/0.70  fof(f676,plain,(
% 2.58/0.70    sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8) | ~v1_funct_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f675,f411])).
% 2.58/0.70  fof(f411,plain,(
% 2.58/0.70    v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8))),
% 2.58/0.70    inference(subsumption_resolution,[],[f410,f83])).
% 2.58/0.70  fof(f410,plain,(
% 2.58/0.70    v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8)) | ~l1_struct_0(sK5)),
% 2.58/0.70    inference(superposition,[],[f405,f106])).
% 2.58/0.70  fof(f675,plain,(
% 2.58/0.70    sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f674,f95])).
% 2.58/0.70  fof(f674,plain,(
% 2.58/0.70    ~v2_funct_1(sK8) | sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f663,f625])).
% 2.58/0.70  fof(f625,plain,(
% 2.58/0.70    k2_relat_1(sK8) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK8),sK8)),
% 2.58/0.70    inference(forward_demodulation,[],[f341,f355])).
% 2.58/0.70  fof(f341,plain,(
% 2.58/0.70    k1_relat_1(sK9) = k2_relset_1(k2_struct_0(sK5),k1_relat_1(sK9),sK8)),
% 2.58/0.70    inference(backward_demodulation,[],[f215,f286])).
% 2.58/0.70  fof(f215,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f214,f85])).
% 2.58/0.70  fof(f214,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK8) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f166,f106])).
% 2.58/0.70  fof(f166,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f152,f83])).
% 2.58/0.70  fof(f152,plain,(
% 2.58/0.70    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK8) | ~l1_struct_0(sK5)),
% 2.58/0.70    inference(superposition,[],[f94,f106])).
% 2.58/0.70  fof(f663,plain,(
% 2.58/0.70    k2_relat_1(sK8) != k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK8),sK8) | ~v2_funct_1(sK8) | sP4(k2_struct_0(sK5),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,k2_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 2.58/0.70    inference(resolution,[],[f135,f563])).
% 2.58/0.70  fof(f879,plain,(
% 2.58/0.70    ~v1_funct_1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK5),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK5),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | spl10_16),
% 2.58/0.70    inference(superposition,[],[f842,f136])).
% 2.58/0.70  fof(f842,plain,(
% 2.58/0.70    ~v1_funct_1(k2_tops_2(u1_struct_0(sK5),k2_relat_1(sK8),sK8)) | spl10_16),
% 2.58/0.70    inference(avatar_component_clause,[],[f840])).
% 2.58/0.70  fof(f871,plain,(
% 2.58/0.70    spl10_15),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f870])).
% 2.58/0.70  fof(f870,plain,(
% 2.58/0.70    $false | spl10_15),
% 2.58/0.70    inference(subsumption_resolution,[],[f868,f483])).
% 2.58/0.70  fof(f483,plain,(
% 2.58/0.70    sP3(k2_relat_1(sK8),k2_relat_1(sK9),sK9)),
% 2.58/0.70    inference(forward_demodulation,[],[f482,f311])).
% 2.58/0.70  fof(f482,plain,(
% 2.58/0.70    sP3(k2_relat_1(sK8),k2_struct_0(sK7),sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f481,f87])).
% 2.58/0.70  fof(f481,plain,(
% 2.58/0.70    sP3(k2_relat_1(sK8),k2_struct_0(sK7),sK9) | ~l1_struct_0(sK7)),
% 2.58/0.70    inference(superposition,[],[f473,f106])).
% 2.58/0.70  fof(f473,plain,(
% 2.58/0.70    sP3(k2_relat_1(sK8),u1_struct_0(sK7),sK9)),
% 2.58/0.70    inference(forward_demodulation,[],[f472,f310])).
% 2.58/0.70  fof(f472,plain,(
% 2.58/0.70    sP3(k2_struct_0(sK6),u1_struct_0(sK7),sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f470,f85])).
% 2.58/0.70  fof(f470,plain,(
% 2.58/0.70    sP3(k2_struct_0(sK6),u1_struct_0(sK7),sK9) | ~l1_struct_0(sK6)),
% 2.58/0.70    inference(superposition,[],[f458,f106])).
% 2.58/0.70  fof(f458,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK6),u1_struct_0(sK7),sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f457,f91])).
% 2.58/0.70  fof(f457,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK6),u1_struct_0(sK7),sK9) | ~v1_funct_1(sK9)),
% 2.58/0.70    inference(subsumption_resolution,[],[f451,f92])).
% 2.58/0.70  fof(f451,plain,(
% 2.58/0.70    sP3(u1_struct_0(sK6),u1_struct_0(sK7),sK9) | ~v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) | ~v1_funct_1(sK9)),
% 2.58/0.70    inference(resolution,[],[f131,f93])).
% 2.58/0.70  fof(f868,plain,(
% 2.58/0.70    ~sP3(k2_relat_1(sK8),k2_relat_1(sK9),sK9) | spl10_15),
% 2.58/0.70    inference(resolution,[],[f838,f130])).
% 2.58/0.70  fof(f838,plain,(
% 2.58/0.70    ~m1_subset_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK9),k2_relat_1(sK8)))) | spl10_15),
% 2.58/0.70    inference(avatar_component_clause,[],[f836])).
% 2.58/0.70  fof(f859,plain,(
% 2.58/0.70    spl10_14),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f858])).
% 2.58/0.70  fof(f858,plain,(
% 2.58/0.70    $false | spl10_14),
% 2.58/0.70    inference(subsumption_resolution,[],[f856,f483])).
% 2.58/0.70  fof(f856,plain,(
% 2.58/0.70    ~sP3(k2_relat_1(sK8),k2_relat_1(sK9),sK9) | spl10_14),
% 2.58/0.70    inference(resolution,[],[f834,f128])).
% 2.58/0.70  fof(f128,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~sP3(X0,X1,X2)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f80])).
% 2.58/0.70  fof(f834,plain,(
% 2.58/0.70    ~v1_funct_1(k2_tops_2(k2_relat_1(sK8),k2_relat_1(sK9),sK9)) | spl10_14),
% 2.58/0.70    inference(avatar_component_clause,[],[f832])).
% 2.58/0.70  fof(f813,plain,(
% 2.58/0.70    ~spl10_2 | spl10_8),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f812])).
% 2.58/0.70  fof(f812,plain,(
% 2.58/0.70    $false | (~spl10_2 | spl10_8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f811,f88])).
% 2.58/0.70  fof(f811,plain,(
% 2.58/0.70    ~v1_funct_1(sK8) | (~spl10_2 | spl10_8)),
% 2.58/0.70    inference(subsumption_resolution,[],[f810,f519])).
% 2.58/0.70  fof(f810,plain,(
% 2.58/0.70    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f809,f91])).
% 2.58/0.70  fof(f809,plain,(
% 2.58/0.70    ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_8),
% 2.58/0.70    inference(subsumption_resolution,[],[f807,f565])).
% 2.58/0.70  fof(f807,plain,(
% 2.58/0.70    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),k2_relat_1(sK9)))) | ~v1_funct_1(sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_relat_1(sK8)))) | ~v1_funct_1(sK8) | spl10_8),
% 2.58/0.70    inference(resolution,[],[f780,f142])).
% 2.58/0.70  fof(f142,plain,(
% 2.58/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f58])).
% 2.58/0.70  fof(f780,plain,(
% 2.58/0.70    ~v1_funct_1(k1_partfun1(u1_struct_0(sK5),k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(sK9),sK8,sK9)) | spl10_8),
% 2.58/0.70    inference(avatar_component_clause,[],[f778])).
% 2.58/0.70  fof(f699,plain,(
% 2.58/0.70    spl10_4),
% 2.58/0.70    inference(avatar_contradiction_clause,[],[f698])).
% 2.58/0.70  fof(f698,plain,(
% 2.58/0.70    $false | spl10_4),
% 2.58/0.70    inference(subsumption_resolution,[],[f697,f87])).
% 2.58/0.70  fof(f697,plain,(
% 2.58/0.70    ~l1_struct_0(sK7) | spl10_4),
% 2.58/0.70    inference(subsumption_resolution,[],[f696,f311])).
% 2.58/0.70  fof(f696,plain,(
% 2.58/0.70    k2_struct_0(sK7) != k2_relat_1(sK9) | ~l1_struct_0(sK7) | spl10_4),
% 2.58/0.70    inference(superposition,[],[f694,f106])).
% 2.58/0.70  fof(f694,plain,(
% 2.58/0.70    u1_struct_0(sK7) != k2_relat_1(sK9) | spl10_4),
% 2.58/0.70    inference(avatar_component_clause,[],[f692])).
% 2.58/0.70  % SZS output end Proof for theBenchmark
% 2.58/0.70  % (4672)------------------------------
% 2.58/0.70  % (4672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.70  % (4672)Termination reason: Refutation
% 2.58/0.70  
% 2.58/0.70  % (4672)Memory used [KB]: 7803
% 2.58/0.70  % (4672)Time elapsed: 0.286 s
% 2.58/0.70  % (4672)------------------------------
% 2.58/0.70  % (4672)------------------------------
% 2.58/0.70  % (4666)Success in time 0.344 s
%------------------------------------------------------------------------------
