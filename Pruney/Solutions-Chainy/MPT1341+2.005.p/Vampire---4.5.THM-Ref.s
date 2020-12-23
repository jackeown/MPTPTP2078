%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:35 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  361 (12002 expanded)
%              Number of leaves         :   28 (4350 expanded)
%              Depth                    :   26
%              Number of atoms          : 1293 (93371 expanded)
%              Number of equality atoms :  376 (33217 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f112,f118,f124,f153,f181,f190,f193,f229,f394,f487,f498,f609,f717,f872,f975,f1092,f1101])).

fof(f1101,plain,
    ( spl3_2
    | spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | spl3_2
    | spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1099,f1054])).

fof(f1054,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k1_xboole_0,sK2)
    | spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f991,f1040])).

fof(f1040,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k1_xboole_0,sK2)
    | spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f540,f1034])).

fof(f1034,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1033,f147])).

fof(f147,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1033,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1021,f989])).

fof(f989,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_xboole_0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f161,f228])).

fof(f228,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_13
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f161,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f160,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f160,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f159,f96])).

fof(f96,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f90,f93])).

fof(f93,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f40,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f42,f87])).

fof(f87,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f39,f48])).

fof(f39,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f159,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f45])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f158,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f94])).

fof(f94,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f92,f93])).

fof(f92,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f44,f87])).

fof(f44,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f135,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f91,f93])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f43,f87])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f1021,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f990,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f990,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f165,f228])).

fof(f165,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f96])).

fof(f163,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f162,plain,
    ( ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f94])).

fof(f136,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f540,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f539,f194])).

fof(f194,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f141,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f539,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f533,f41])).

fof(f533,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f991,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f180,f540])).

fof(f180,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_10
  <=> k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1099,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k1_xboole_0,sK2)
    | spl3_2
    | spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1098,f1094])).

fof(f1094,plain,
    ( k5_relat_1(k1_xboole_0,sK2) = k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k1_xboole_0,sK2)
    | spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1085,f1036])).

fof(f1036,plain,
    ( v1_funct_1(k1_xboole_0)
    | spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f157,f1034])).

fof(f157,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f156,f41])).

fof(f156,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f155,f96])).

fof(f155,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f154,f45])).

fof(f154,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f94])).

fof(f134,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1085,plain,
    ( k5_relat_1(k1_xboole_0,sK2) = k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k1_xboole_0,sK2)
    | ~ v1_funct_1(k1_xboole_0)
    | spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f982,f1050])).

fof(f1050,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)))
    | spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f990,f1034])).

fof(f982,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_xboole_0,k2_struct_0(sK1),X2,sK2)
        | ~ v1_funct_1(X2) )
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f172,f228])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1098,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k1_xboole_0,sK2)
    | spl3_2
    | spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1097,f1048])).

fof(f1048,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2)
    | spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f983,f1034])).

fof(f983,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f169,f228])).

fof(f169,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f168,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f167,f96])).

fof(f167,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f94])).

fof(f166,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f1097,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2),sK2)
    | spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1096,f986])).

fof(f986,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f94,f228])).

fof(f1096,plain,
    ( k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1095,f888])).

fof(f888,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f87,f228])).

fof(f1095,plain,
    ( k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f84,f93])).

fof(f84,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_2
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) = k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1092,plain,
    ( spl3_1
    | ~ spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f1091])).

fof(f1091,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1090,f1052])).

fof(f1052,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0)
    | spl3_1
    | spl3_8
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f1000,f1034])).

fof(f1000,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f999,f983])).

fof(f999,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f998,f985])).

fof(f985,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f984,f228])).

fof(f984,plain,
    ( k1_xboole_0 = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f131,f907])).

fof(f907,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f152,f228])).

fof(f152,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_9
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f131,plain,(
    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f95,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f998,plain,
    ( k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f997,f888])).

fof(f997,plain,
    ( k1_partfun1(u1_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f80,f93])).

fof(f80,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_1
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1090,plain,
    ( k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_4
    | spl3_8
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1089,f1041])).

fof(f1041,plain,
    ( k6_relat_1(k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_4
    | spl3_8
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f901,f1034])).

fof(f901,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f111,f899])).

fof(f899,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f887,f228])).

fof(f887,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f189,f111])).

fof(f189,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_11
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f111,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_4
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1089,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0)
    | spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1087,f41])).

fof(f1087,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f1067,f987])).

fof(f987,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f95,f228])).

fof(f1067,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k1_xboole_0)
        | ~ v1_funct_1(X2) )
    | spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f1066,f1036])).

fof(f1066,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1065,f1034])).

fof(f1065,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k1_xboole_0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f1029,f1034])).

fof(f1029,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f990,f68])).

fof(f975,plain,
    ( spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f973,f898])).

fof(f898,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f886,f228])).

fof(f886,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(sK2),sK2)
    | spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f885,f877])).

fof(f877,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f169,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f885,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2),sK2)
    | spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f884,f875])).

fof(f875,plain,
    ( k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f94,f148])).

fof(f884,plain,
    ( k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2),sK2) != k6_relat_1(k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2))
    | spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f883,f87])).

fof(f883,plain,
    ( k1_partfun1(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK0),k1_xboole_0,k2_tops_2(u1_struct_0(sK0),k1_xboole_0,sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2))
    | spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f84,f803])).

fof(f803,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f93,f148])).

fof(f973,plain,
    ( k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f968,f972])).

fof(f972,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f922,f958])).

fof(f958,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f123,f957])).

fof(f957,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f945,f956])).

fof(f956,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f942,f890])).

fof(f890,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f818,f228])).

fof(f818,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f161,f148])).

fof(f942,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f889,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f889,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f816,f228])).

fof(f816,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f165,f148])).

fof(f945,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f889,f55])).

fof(f123,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_6
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f922,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f921,f194])).

fof(f921,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f915,f41])).

fof(f915,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f53])).

fof(f968,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f966,f157])).

fof(f966,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f896,f889])).

fof(f896,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_xboole_0,k1_xboole_0,X2,sK2)
        | ~ v1_funct_1(X2) )
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f878,f228])).

fof(f878,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k1_xboole_0,X2,sK2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f172,f148])).

fof(f872,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f871])).

fof(f871,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_8
    | spl3_10
    | ~ spl3_12 ),
    inference(trivial_inequality_removal,[],[f870])).

fof(f870,plain,
    ( k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_8
    | spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f802,f863])).

fof(f863,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f729,f862])).

fof(f862,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f850,f861])).

fof(f861,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f848,f819])).

fof(f819,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f818,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f848,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f817,f76])).

fof(f817,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f816,f224])).

fof(f850,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f817,f55])).

fof(f729,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f123,f224])).

fof(f802,plain,
    ( k6_relat_1(k1_xboole_0) != k6_relat_1(k2_relat_1(k1_xboole_0))
    | ~ spl3_8
    | spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f763,f148])).

fof(f763,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(k1_xboole_0))
    | spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f762,f742])).

fof(f742,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_relat_1(k2_relat_1(k1_xboole_0))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f540,f224])).

fof(f762,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f179,f224])).

fof(f179,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f717,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(subsumption_resolution,[],[f715,f672])).

fof(f672,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(backward_demodulation,[],[f622,f663])).

fof(f663,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(forward_demodulation,[],[f662,f660])).

fof(f660,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f649,f123])).

fof(f649,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f620,f55])).

fof(f620,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f165,f152])).

fof(f662,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9
    | spl3_13 ),
    inference(subsumption_resolution,[],[f661,f648])).

fof(f648,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_9
    | spl3_13 ),
    inference(superposition,[],[f227,f152])).

fof(f227,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f226])).

fof(f661,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f650,f619])).

fof(f619,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f161,f152])).

fof(f650,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f620,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f622,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k1_relat_1(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k1_relat_1(sK2),sK2,k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f170,f152])).

fof(f170,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f142,f169])).

fof(f142,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relat_1(sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f98,f131])).

fof(f98,plain,
    ( k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f88,f93])).

fof(f88,plain,
    ( k1_partfun1(k2_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f80,f87])).

fof(f715,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(forward_demodulation,[],[f714,f111])).

fof(f714,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(subsumption_resolution,[],[f712,f41])).

fof(f712,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(resolution,[],[f681,f666])).

fof(f666,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(backward_demodulation,[],[f616,f663])).

fof(f616,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f95,f152])).

fof(f681,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k2_relat_1(sK2),k1_relat_1(sK2),X2,k2_funct_1(sK2))
        | ~ v1_funct_1(X2) )
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(forward_demodulation,[],[f680,f663])).

fof(f680,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,k2_struct_0(sK1),k1_relat_1(sK2),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f656,f157])).

fof(f656,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,k2_struct_0(sK1),k1_relat_1(sK2),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_9 ),
    inference(resolution,[],[f620,f68])).

fof(f609,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | spl3_1
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f607])).

fof(f607,plain,
    ( k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0)
    | spl3_1
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f606,f560])).

fof(f560,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f545,f556])).

fof(f556,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f542,f525])).

fof(f525,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f512,f228])).

fof(f512,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f96,f148])).

fof(f542,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f526,f76])).

fof(f526,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f513,f228])).

fof(f513,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f95,f148])).

fof(f545,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f526,f55])).

fof(f606,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_xboole_0)
    | spl3_1
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f520,f605])).

fof(f605,plain,
    ( k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f599,f604])).

fof(f604,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f537,f560])).

fof(f537,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f536,f194])).

fof(f536,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f532,f41])).

fof(f532,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f599,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f597,f41])).

fof(f597,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f590,f526])).

fof(f590,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k1_xboole_0,k1_xboole_0,X2,k2_funct_1(sK2))
        | ~ v1_funct_1(X2) )
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f579,f157])).

fof(f579,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k1_xboole_0,k1_xboole_0,X2,k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(resolution,[],[f522,f68])).

fof(f522,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f508,f228])).

fof(f508,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f165,f148])).

fof(f520,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f505,f228])).

fof(f505,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f170,f148])).

fof(f498,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f496,f432])).

fof(f432,plain,
    ( k6_relat_1(k1_relat_1(k1_xboole_0)) != k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f409,f148])).

fof(f409,plain,
    ( k6_relat_1(k1_relat_1(k1_xboole_0)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f170,f224])).

fof(f496,plain,
    ( k6_relat_1(k1_relat_1(k1_xboole_0)) = k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f495,f400])).

fof(f400,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_relat_1(k1_relat_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f111,f224])).

fof(f495,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f493,f395])).

fof(f395,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f41,f224])).

fof(f493,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f479,f426])).

fof(f426,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f398,f148])).

fof(f398,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f95,f224])).

fof(f479,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(X0,X1,k1_xboole_0,k2_struct_0(sK0),X2,k2_funct_1(k1_xboole_0)) = k5_relat_1(X2,k2_funct_1(k1_xboole_0))
        | ~ v1_funct_1(X2) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f468,f405])).

fof(f405,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f157,f224])).

fof(f468,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,k1_xboole_0,k2_struct_0(sK0),X2,k2_funct_1(k1_xboole_0)) = k5_relat_1(X2,k2_funct_1(k1_xboole_0))
        | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f430,f68])).

fof(f430,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f407,f148])).

fof(f407,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f165,f224])).

fof(f487,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f485,f438])).

fof(f438,plain,
    ( k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f435,f434])).

fof(f434,plain,
    ( k6_relat_1(k1_xboole_0) = k6_relat_1(k2_relat_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f413,f148])).

fof(f413,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f231,f224])).

fof(f231,plain,
    ( k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f180,f117])).

fof(f117,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_5
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f435,plain,
    ( k6_relat_1(k2_relat_1(k1_xboole_0)) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f414,f148])).

fof(f414,plain,
    ( k6_relat_1(k2_relat_1(k1_xboole_0)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f232,f224])).

fof(f232,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f171,f231])).

fof(f171,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f97,f169])).

fof(f97,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f89,f93])).

fof(f89,plain,
    ( k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(u1_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f86,f87])).

fof(f86,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1))
    | spl3_2 ),
    inference(forward_demodulation,[],[f84,f44])).

fof(f485,plain,
    ( k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f484,f437])).

fof(f437,plain,
    ( k6_relat_1(k1_xboole_0) = k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f401,f434])).

fof(f401,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_relat_1(k2_relat_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f117,f224])).

fof(f484,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f482,f405])).

fof(f482,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f433,f430])).

fof(f433,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK0),k1_xboole_0,X2,k1_xboole_0)
        | ~ v1_funct_1(X2) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f410,f148])).

fof(f410,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f172,f224])).

fof(f394,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_13 ),
    inference(subsumption_resolution,[],[f392,f287])).

fof(f287,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_13 ),
    inference(backward_demodulation,[],[f243,f276])).

fof(f276,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(forward_demodulation,[],[f275,f273])).

fof(f273,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f262,f123])).

fof(f262,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f239,f55])).

fof(f239,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f165,f152])).

fof(f275,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9
    | spl3_13 ),
    inference(subsumption_resolution,[],[f274,f261])).

fof(f261,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_9
    | spl3_13 ),
    inference(superposition,[],[f227,f152])).

fof(f274,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f263,f238])).

fof(f238,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f161,f152])).

fof(f263,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f239,f56])).

fof(f243,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK1),k1_relat_1(sK2),k1_relat_1(sK2),k2_struct_0(sK1),k2_funct_1(sK2),sK2)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f232,f152])).

fof(f392,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(forward_demodulation,[],[f391,f117])).

fof(f391,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(subsumption_resolution,[],[f389,f157])).

fof(f389,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(resolution,[],[f286,f283])).

fof(f283,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(backward_demodulation,[],[f239,f276])).

fof(f286,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_relat_1(sK2),k2_relat_1(sK2),X2,sK2)
        | ~ v1_funct_1(X2) )
    | ~ spl3_6
    | ~ spl3_9
    | spl3_13 ),
    inference(backward_demodulation,[],[f242,f276])).

fof(f242,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_relat_1(sK2),k2_struct_0(sK1),X2,sK2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f172,f152])).

fof(f229,plain,
    ( spl3_12
    | spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f220,f146,f226,f222])).

fof(f220,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f208,f198])).

fof(f198,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f96,f148])).

fof(f208,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(resolution,[],[f197,f74])).

fof(f197,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f95,f148])).

fof(f193,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f191,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f141,f107])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f190,plain,
    ( spl3_11
    | spl3_8 ),
    inference(avatar_split_clause,[],[f185,f146,f187])).

fof(f185,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f184,f41])).

fof(f184,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f183,f96])).

fof(f183,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f182,f94])).

fof(f182,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f140,f45])).

fof(f140,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f66,f47])).

fof(f47,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f181,plain,
    ( spl3_10
    | spl3_8 ),
    inference(avatar_split_clause,[],[f176,f146,f178])).

fof(f176,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f175,f41])).

fof(f175,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f96])).

fof(f174,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f173,f94])).

fof(f173,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f139,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f67,f47])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f153,plain,
    ( spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f144,f150,f146])).

fof(f144,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f143,f131])).

fof(f143,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f132,f96])).

fof(f132,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f95,f56])).

fof(f124,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_split_clause,[],[f119,f121,f105])).

fof(f119,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f101,f41])).

fof(f101,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f118,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f113,f115,f105])).

fof(f113,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f100,f41])).

fof(f100,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f53])).

fof(f112,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f52])).

fof(f85,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f69,f82,f78])).

fof(f69,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:47:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (9327)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (9345)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (9329)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.56  % (9330)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.57  % (9333)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.57  % (9337)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.57  % (9335)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (9344)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.58  % (9341)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.58  % (9332)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.58  % (9349)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.58  % (9341)Refutation not found, incomplete strategy% (9341)------------------------------
% 1.70/0.58  % (9341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (9326)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.70/0.59  % (9341)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  % (9347)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.70/0.59  
% 1.70/0.59  % (9341)Memory used [KB]: 10618
% 1.70/0.59  % (9341)Time elapsed: 0.152 s
% 1.70/0.59  % (9341)------------------------------
% 1.70/0.59  % (9341)------------------------------
% 1.70/0.60  % (9351)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.70/0.60  % (9333)Refutation not found, incomplete strategy% (9333)------------------------------
% 1.70/0.60  % (9333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (9333)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (9333)Memory used [KB]: 10874
% 1.70/0.60  % (9333)Time elapsed: 0.167 s
% 1.70/0.60  % (9333)------------------------------
% 1.70/0.60  % (9333)------------------------------
% 1.70/0.60  % (9339)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.70/0.60  % (9339)Refutation not found, incomplete strategy% (9339)------------------------------
% 1.70/0.60  % (9339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (9339)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (9339)Memory used [KB]: 6140
% 1.70/0.60  % (9339)Time elapsed: 0.003 s
% 1.70/0.60  % (9339)------------------------------
% 1.70/0.60  % (9339)------------------------------
% 1.70/0.60  % (9325)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.70/0.60  % (9343)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.70/0.60  % (9324)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.70/0.60  % (9346)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.70/0.60  % (9334)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.70/0.61  % (9328)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.70/0.61  % (9334)Refutation not found, incomplete strategy% (9334)------------------------------
% 1.70/0.61  % (9334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (9338)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.70/0.61  % (9331)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.70/0.62  % (9352)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.70/0.62  % (9340)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.62  % (9342)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.70/0.62  % (9350)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.70/0.62  % (9324)Refutation not found, incomplete strategy% (9324)------------------------------
% 1.70/0.62  % (9324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (9353)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.62  % (9324)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.62  
% 1.70/0.62  % (9324)Memory used [KB]: 1918
% 1.70/0.62  % (9324)Time elapsed: 0.176 s
% 1.70/0.62  % (9324)------------------------------
% 1.70/0.62  % (9324)------------------------------
% 1.70/0.62  % (9348)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.70/0.63  % (9335)Refutation not found, incomplete strategy% (9335)------------------------------
% 1.70/0.63  % (9335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.63  % (9335)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.63  
% 1.70/0.63  % (9335)Memory used [KB]: 10874
% 1.70/0.63  % (9335)Time elapsed: 0.200 s
% 1.70/0.63  % (9335)------------------------------
% 1.70/0.63  % (9335)------------------------------
% 1.70/0.63  % (9336)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.70/0.63  % (9332)Refutation found. Thanks to Tanya!
% 1.70/0.63  % SZS status Theorem for theBenchmark
% 1.70/0.63  % (9334)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.63  
% 1.70/0.63  % (9334)Memory used [KB]: 10746
% 1.70/0.63  % (9334)Time elapsed: 0.184 s
% 1.70/0.63  % (9334)------------------------------
% 1.70/0.63  % (9334)------------------------------
% 1.70/0.64  % SZS output start Proof for theBenchmark
% 1.70/0.64  fof(f1106,plain,(
% 1.70/0.64    $false),
% 1.70/0.64    inference(avatar_sat_refutation,[],[f85,f112,f118,f124,f153,f181,f190,f193,f229,f394,f487,f498,f609,f717,f872,f975,f1092,f1101])).
% 1.70/0.64  fof(f1101,plain,(
% 1.70/0.64    spl3_2 | spl3_8 | ~spl3_10 | ~spl3_13),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f1100])).
% 1.70/0.64  fof(f1100,plain,(
% 1.70/0.64    $false | (spl3_2 | spl3_8 | ~spl3_10 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f1099,f1054])).
% 1.70/0.64  fof(f1054,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k1_xboole_0,sK2) | (spl3_8 | ~spl3_10 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f991,f1040])).
% 1.70/0.64  fof(f1040,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k1_xboole_0,sK2) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f540,f1034])).
% 1.70/0.64  fof(f1034,plain,(
% 1.70/0.64    k1_xboole_0 = k2_funct_1(sK2) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f1033,f147])).
% 1.70/0.64  fof(f147,plain,(
% 1.70/0.64    k1_xboole_0 != k2_struct_0(sK1) | spl3_8),
% 1.70/0.64    inference(avatar_component_clause,[],[f146])).
% 1.70/0.64  fof(f146,plain,(
% 1.70/0.64    spl3_8 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.70/0.64  fof(f1033,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 = k2_funct_1(sK2) | ~spl3_13),
% 1.70/0.64    inference(subsumption_resolution,[],[f1021,f989])).
% 1.70/0.64  fof(f989,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_xboole_0) | ~spl3_13),
% 1.70/0.64    inference(forward_demodulation,[],[f161,f228])).
% 1.70/0.64  fof(f228,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_13),
% 1.70/0.64    inference(avatar_component_clause,[],[f226])).
% 1.70/0.64  fof(f226,plain,(
% 1.70/0.64    spl3_13 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.70/0.64  fof(f161,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.70/0.64    inference(subsumption_resolution,[],[f160,f41])).
% 1.70/0.64  fof(f41,plain,(
% 1.70/0.64    v1_funct_1(sK2)),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f37,plain,(
% 1.70/0.64    (((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).
% 1.70/0.64  fof(f34,plain,(
% 1.70/0.64    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f35,plain,(
% 1.70/0.64    ? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f36,plain,(
% 1.70/0.64    ? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f16,plain,(
% 1.70/0.64    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.70/0.64    inference(flattening,[],[f15])).
% 1.70/0.64  fof(f15,plain,(
% 1.70/0.64    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.70/0.64    inference(ennf_transformation,[],[f14])).
% 1.70/0.64  fof(f14,negated_conjecture,(
% 1.70/0.64    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.70/0.64    inference(negated_conjecture,[],[f13])).
% 1.70/0.64  fof(f13,conjecture,(
% 1.70/0.64    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).
% 1.70/0.64  fof(f160,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f159,f96])).
% 1.70/0.64  fof(f96,plain,(
% 1.70/0.64    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.70/0.64    inference(backward_demodulation,[],[f90,f93])).
% 1.70/0.64  fof(f93,plain,(
% 1.70/0.64    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.70/0.64    inference(resolution,[],[f40,f48])).
% 1.70/0.64  fof(f48,plain,(
% 1.70/0.64    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f17])).
% 1.70/0.64  fof(f17,plain,(
% 1.70/0.64    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.70/0.64    inference(ennf_transformation,[],[f11])).
% 1.70/0.64  fof(f11,axiom,(
% 1.70/0.64    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.70/0.64  fof(f40,plain,(
% 1.70/0.64    l1_struct_0(sK1)),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f90,plain,(
% 1.70/0.64    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.70/0.64    inference(backward_demodulation,[],[f42,f87])).
% 1.70/0.64  fof(f87,plain,(
% 1.70/0.64    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.70/0.64    inference(resolution,[],[f39,f48])).
% 1.70/0.64  fof(f39,plain,(
% 1.70/0.64    l1_struct_0(sK0)),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f42,plain,(
% 1.70/0.64    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f159,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f158,f45])).
% 1.70/0.64  fof(f45,plain,(
% 1.70/0.64    v2_funct_1(sK2)),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f158,plain,(
% 1.70/0.64    ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f135,f94])).
% 1.70/0.64  fof(f94,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.70/0.64    inference(backward_demodulation,[],[f92,f93])).
% 1.70/0.64  fof(f92,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.70/0.64    inference(backward_demodulation,[],[f44,f87])).
% 1.70/0.64  fof(f44,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f135,plain,(
% 1.70/0.64    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f63])).
% 1.70/0.64  fof(f63,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f27])).
% 1.70/0.64  fof(f27,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.70/0.64    inference(flattening,[],[f26])).
% 1.70/0.64  fof(f26,plain,(
% 1.70/0.64    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.70/0.64    inference(ennf_transformation,[],[f9])).
% 1.70/0.64  fof(f9,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.70/0.64  fof(f95,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.70/0.64    inference(backward_demodulation,[],[f91,f93])).
% 1.70/0.64  fof(f91,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.70/0.64    inference(backward_demodulation,[],[f43,f87])).
% 1.70/0.64  fof(f43,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  fof(f1021,plain,(
% 1.70/0.64    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 = k2_funct_1(sK2) | ~spl3_13),
% 1.70/0.64    inference(resolution,[],[f990,f74])).
% 1.70/0.64  fof(f74,plain,(
% 1.70/0.64    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.70/0.64    inference(equality_resolution,[],[f60])).
% 1.70/0.64  fof(f60,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f38])).
% 1.70/0.64  fof(f38,plain,(
% 1.70/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.64    inference(nnf_transformation,[],[f25])).
% 1.70/0.64  fof(f25,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.64    inference(flattening,[],[f24])).
% 1.70/0.64  fof(f24,plain,(
% 1.70/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.64    inference(ennf_transformation,[],[f6])).
% 1.70/0.64  fof(f6,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.70/0.64  fof(f990,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) | ~spl3_13),
% 1.70/0.64    inference(forward_demodulation,[],[f165,f228])).
% 1.70/0.64  fof(f165,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.70/0.64    inference(subsumption_resolution,[],[f164,f41])).
% 1.70/0.64  fof(f164,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f163,f96])).
% 1.70/0.64  fof(f163,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f162,f45])).
% 1.70/0.64  fof(f162,plain,(
% 1.70/0.64    ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f136,f94])).
% 1.70/0.64  fof(f136,plain,(
% 1.70/0.64    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f64])).
% 1.70/0.64  fof(f64,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f27])).
% 1.70/0.64  fof(f540,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 1.70/0.64    inference(subsumption_resolution,[],[f539,f194])).
% 1.70/0.64  fof(f194,plain,(
% 1.70/0.64    v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f141,f54])).
% 1.70/0.64  fof(f54,plain,(
% 1.70/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f2])).
% 1.70/0.64  fof(f2,axiom,(
% 1.70/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.70/0.64  fof(f141,plain,(
% 1.70/0.64    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 1.70/0.64    inference(resolution,[],[f95,f49])).
% 1.70/0.64  fof(f49,plain,(
% 1.70/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f18])).
% 1.70/0.64  fof(f18,plain,(
% 1.70/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.70/0.64    inference(ennf_transformation,[],[f1])).
% 1.70/0.64  fof(f1,axiom,(
% 1.70/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.70/0.64  fof(f539,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f533,f41])).
% 1.70/0.64  fof(f533,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f45,f53])).
% 1.70/0.64  fof(f53,plain,(
% 1.70/0.64    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f22])).
% 1.70/0.64  fof(f22,plain,(
% 1.70/0.64    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.64    inference(flattening,[],[f21])).
% 1.70/0.64  fof(f21,plain,(
% 1.70/0.64    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.70/0.64    inference(ennf_transformation,[],[f4])).
% 1.70/0.64  fof(f4,axiom,(
% 1.70/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.70/0.64  fof(f991,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_10),
% 1.70/0.64    inference(forward_demodulation,[],[f180,f540])).
% 1.70/0.64  fof(f180,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~spl3_10),
% 1.70/0.64    inference(avatar_component_clause,[],[f178])).
% 1.70/0.64  fof(f178,plain,(
% 1.70/0.64    spl3_10 <=> k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.70/0.64  fof(f1099,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k1_xboole_0,sK2) | (spl3_2 | spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1098,f1094])).
% 1.70/0.64  fof(f1094,plain,(
% 1.70/0.64    k5_relat_1(k1_xboole_0,sK2) = k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k1_xboole_0,sK2) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f1085,f1036])).
% 1.70/0.64  fof(f1036,plain,(
% 1.70/0.64    v1_funct_1(k1_xboole_0) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f157,f1034])).
% 1.70/0.64  fof(f157,plain,(
% 1.70/0.64    v1_funct_1(k2_funct_1(sK2))),
% 1.70/0.64    inference(subsumption_resolution,[],[f156,f41])).
% 1.70/0.64  fof(f156,plain,(
% 1.70/0.64    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f155,f96])).
% 1.70/0.64  fof(f155,plain,(
% 1.70/0.64    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f154,f45])).
% 1.70/0.64  fof(f154,plain,(
% 1.70/0.64    ~v2_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f134,f94])).
% 1.70/0.64  fof(f134,plain,(
% 1.70/0.64    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f62])).
% 1.70/0.64  fof(f62,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_1(k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f27])).
% 1.70/0.64  fof(f1085,plain,(
% 1.70/0.64    k5_relat_1(k1_xboole_0,sK2) = k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k1_xboole_0,sK2) | ~v1_funct_1(k1_xboole_0) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f982,f1050])).
% 1.70/0.64  fof(f1050,plain,(
% 1.70/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f990,f1034])).
% 1.70/0.64  fof(f982,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_xboole_0,k2_struct_0(sK1),X2,sK2) | ~v1_funct_1(X2)) ) | ~spl3_13),
% 1.70/0.64    inference(forward_demodulation,[],[f172,f228])).
% 1.70/0.64  fof(f172,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(subsumption_resolution,[],[f138,f41])).
% 1.70/0.64  fof(f138,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,sK2) = k5_relat_1(X2,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(resolution,[],[f95,f68])).
% 1.70/0.64  fof(f68,plain,(
% 1.70/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f33])).
% 1.70/0.64  fof(f33,plain,(
% 1.70/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.70/0.64    inference(flattening,[],[f32])).
% 1.70/0.64  fof(f32,plain,(
% 1.70/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.70/0.64    inference(ennf_transformation,[],[f7])).
% 1.70/0.64  fof(f7,axiom,(
% 1.70/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.70/0.64  fof(f1098,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k1_xboole_0,sK2) | (spl3_2 | spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1097,f1048])).
% 1.70/0.64  fof(f1048,plain,(
% 1.70/0.64    k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f983,f1034])).
% 1.70/0.64  fof(f983,plain,(
% 1.70/0.64    k2_funct_1(sK2) = k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2) | ~spl3_13),
% 1.70/0.64    inference(forward_demodulation,[],[f169,f228])).
% 1.70/0.64  fof(f169,plain,(
% 1.70/0.64    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f168,f41])).
% 1.70/0.64  fof(f168,plain,(
% 1.70/0.64    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f167,f96])).
% 1.70/0.64  fof(f167,plain,(
% 1.70/0.64    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f166,f94])).
% 1.70/0.64  fof(f166,plain,(
% 1.70/0.64    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f137,f45])).
% 1.70/0.64  fof(f137,plain,(
% 1.70/0.64    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f65])).
% 1.70/0.64  fof(f65,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f29])).
% 1.70/0.64  fof(f29,plain,(
% 1.70/0.64    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.70/0.64    inference(flattening,[],[f28])).
% 1.70/0.64  fof(f28,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.70/0.64    inference(ennf_transformation,[],[f12])).
% 1.70/0.64  fof(f12,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.70/0.64  fof(f1097,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2),sK2) | (spl3_2 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1096,f986])).
% 1.70/0.64  fof(f986,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k2_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) | ~spl3_13),
% 1.70/0.64    inference(forward_demodulation,[],[f94,f228])).
% 1.70/0.64  fof(f1096,plain,(
% 1.70/0.64    k1_partfun1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_struct_0(sK1),k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1095,f888])).
% 1.70/0.64  fof(f888,plain,(
% 1.70/0.64    k1_xboole_0 = u1_struct_0(sK0) | ~spl3_13),
% 1.70/0.64    inference(backward_demodulation,[],[f87,f228])).
% 1.70/0.64  fof(f1095,plain,(
% 1.70/0.64    k1_partfun1(k2_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_2),
% 1.70/0.64    inference(forward_demodulation,[],[f84,f93])).
% 1.70/0.64  fof(f84,plain,(
% 1.70/0.64    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 1.70/0.64    inference(avatar_component_clause,[],[f82])).
% 1.70/0.64  fof(f82,plain,(
% 1.70/0.64    spl3_2 <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) = k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.70/0.64  fof(f1092,plain,(
% 1.70/0.64    spl3_1 | ~spl3_4 | spl3_8 | ~spl3_9 | ~spl3_11 | ~spl3_13),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f1091])).
% 1.70/0.64  fof(f1091,plain,(
% 1.70/0.64    $false | (spl3_1 | ~spl3_4 | spl3_8 | ~spl3_9 | ~spl3_11 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f1090,f1052])).
% 1.70/0.64  fof(f1052,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0) | (spl3_1 | spl3_8 | ~spl3_9 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f1000,f1034])).
% 1.70/0.64  fof(f1000,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k2_funct_1(sK2)) | (spl3_1 | ~spl3_9 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f999,f983])).
% 1.70/0.64  fof(f999,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_9 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f998,f985])).
% 1.70/0.64  fof(f985,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2) | (~spl3_9 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f984,f228])).
% 1.70/0.64  fof(f984,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_9 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f131,f907])).
% 1.70/0.64  fof(f907,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relat_1(sK2) | (~spl3_9 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f152,f228])).
% 1.70/0.64  fof(f152,plain,(
% 1.70/0.64    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_9),
% 1.70/0.64    inference(avatar_component_clause,[],[f150])).
% 1.70/0.64  fof(f150,plain,(
% 1.70/0.64    spl3_9 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.70/0.64  fof(f131,plain,(
% 1.70/0.64    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f55])).
% 1.70/0.64  fof(f55,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f23])).
% 1.70/0.64  fof(f23,plain,(
% 1.70/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.64    inference(ennf_transformation,[],[f5])).
% 1.70/0.64  fof(f5,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.70/0.64  fof(f998,plain,(
% 1.70/0.64    k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k2_tops_2(k1_xboole_0,k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k1_xboole_0,k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f997,f888])).
% 1.70/0.64  fof(f997,plain,(
% 1.70/0.64    k1_partfun1(u1_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_1),
% 1.70/0.64    inference(forward_demodulation,[],[f80,f93])).
% 1.70/0.64  fof(f80,plain,(
% 1.70/0.64    k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 1.70/0.64    inference(avatar_component_clause,[],[f78])).
% 1.70/0.64  fof(f78,plain,(
% 1.70/0.64    spl3_1 <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.70/0.64  fof(f1090,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0) | (~spl3_4 | spl3_8 | ~spl3_11 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1089,f1041])).
% 1.70/0.64  fof(f1041,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0) | (~spl3_4 | spl3_8 | ~spl3_11 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f901,f1034])).
% 1.70/0.64  fof(f901,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_xboole_0) | (~spl3_4 | ~spl3_11 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f111,f899])).
% 1.70/0.64  fof(f899,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k1_xboole_0) | (~spl3_4 | ~spl3_11 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f887,f228])).
% 1.70/0.64  fof(f887,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | (~spl3_4 | ~spl3_11)),
% 1.70/0.64    inference(backward_demodulation,[],[f189,f111])).
% 1.70/0.64  fof(f189,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | ~spl3_11),
% 1.70/0.64    inference(avatar_component_clause,[],[f187])).
% 1.70/0.64  fof(f187,plain,(
% 1.70/0.64    spl3_11 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.70/0.64  fof(f111,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_4),
% 1.70/0.64    inference(avatar_component_clause,[],[f109])).
% 1.70/0.64  fof(f109,plain,(
% 1.70/0.64    spl3_4 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.70/0.64  fof(f1089,plain,(
% 1.70/0.64    k5_relat_1(sK2,k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f1087,f41])).
% 1.70/0.64  fof(f1087,plain,(
% 1.70/0.64    k5_relat_1(sK2,k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0,sK2,k1_xboole_0) | ~v1_funct_1(sK2) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f1067,f987])).
% 1.70/0.64  fof(f987,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | ~spl3_13),
% 1.70/0.64    inference(forward_demodulation,[],[f95,f228])).
% 1.70/0.64  fof(f1067,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k1_xboole_0) | ~v1_funct_1(X2)) ) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f1066,f1036])).
% 1.70/0.64  fof(f1066,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(k1_xboole_0) | k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1065,f1034])).
% 1.70/0.64  fof(f1065,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f1029,f1034])).
% 1.70/0.64  fof(f1029,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k2_struct_0(sK1),k1_xboole_0,X2,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_13),
% 1.70/0.64    inference(resolution,[],[f990,f68])).
% 1.70/0.64  fof(f975,plain,(
% 1.70/0.64    spl3_2 | ~spl3_6 | ~spl3_8 | ~spl3_13),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f974])).
% 1.70/0.64  fof(f974,plain,(
% 1.70/0.64    $false | (spl3_2 | ~spl3_6 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f973,f898])).
% 1.70/0.64  fof(f898,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2) | (spl3_2 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f886,f228])).
% 1.70/0.64  fof(f886,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(sK2),sK2) | (spl3_2 | ~spl3_8)),
% 1.70/0.64    inference(forward_demodulation,[],[f885,f877])).
% 1.70/0.64  fof(f877,plain,(
% 1.70/0.64    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f169,f148])).
% 1.70/0.64  fof(f148,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_8),
% 1.70/0.64    inference(avatar_component_clause,[],[f146])).
% 1.70/0.64  fof(f885,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2),sK2) | (spl3_2 | ~spl3_8)),
% 1.70/0.64    inference(forward_demodulation,[],[f884,f875])).
% 1.70/0.64  fof(f875,plain,(
% 1.70/0.64    k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f94,f148])).
% 1.70/0.64  fof(f884,plain,(
% 1.70/0.64    k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k2_struct_0(sK0),k1_xboole_0,sK2),sK2) != k6_relat_1(k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)) | (spl3_2 | ~spl3_8)),
% 1.70/0.64    inference(forward_demodulation,[],[f883,f87])).
% 1.70/0.64  fof(f883,plain,(
% 1.70/0.64    k1_partfun1(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK0),k1_xboole_0,k2_tops_2(u1_struct_0(sK0),k1_xboole_0,sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2)) | (spl3_2 | ~spl3_8)),
% 1.70/0.64    inference(forward_demodulation,[],[f84,f803])).
% 1.70/0.64  fof(f803,plain,(
% 1.70/0.64    k1_xboole_0 = u1_struct_0(sK1) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f93,f148])).
% 1.70/0.64  fof(f973,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2) | (~spl3_6 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f968,f972])).
% 1.70/0.64  fof(f972,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k1_xboole_0) | (~spl3_6 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f922,f958])).
% 1.70/0.64  fof(f958,plain,(
% 1.70/0.64    k1_xboole_0 = k2_relat_1(sK2) | (~spl3_6 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f123,f957])).
% 1.70/0.64  fof(f957,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f945,f956])).
% 1.70/0.64  fof(f956,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f942,f890])).
% 1.70/0.64  fof(f890,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f818,f228])).
% 1.70/0.64  fof(f818,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f161,f148])).
% 1.70/0.64  fof(f942,plain,(
% 1.70/0.64    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f889,f76])).
% 1.70/0.64  fof(f76,plain,(
% 1.70/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.70/0.64    inference(equality_resolution,[],[f57])).
% 1.70/0.64  fof(f57,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f38])).
% 1.70/0.64  fof(f889,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f816,f228])).
% 1.70/0.64  fof(f816,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f165,f148])).
% 1.70/0.64  fof(f945,plain,(
% 1.70/0.64    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f889,f55])).
% 1.70/0.64  fof(f123,plain,(
% 1.70/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 1.70/0.64    inference(avatar_component_clause,[],[f121])).
% 1.70/0.64  fof(f121,plain,(
% 1.70/0.64    spl3_6 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.70/0.64  fof(f922,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 1.70/0.64    inference(subsumption_resolution,[],[f921,f194])).
% 1.70/0.64  fof(f921,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f915,f41])).
% 1.70/0.64  fof(f915,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f45,f53])).
% 1.70/0.64  fof(f968,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f966,f157])).
% 1.70/0.64  fof(f966,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK2),sK2) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f896,f889])).
% 1.70/0.64  fof(f896,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_xboole_0,k1_xboole_0,X2,sK2) | ~v1_funct_1(X2)) ) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f878,f228])).
% 1.70/0.64  fof(f878,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k1_xboole_0,X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f172,f148])).
% 1.70/0.64  fof(f872,plain,(
% 1.70/0.64    ~spl3_6 | ~spl3_8 | spl3_10 | ~spl3_12),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f871])).
% 1.70/0.64  fof(f871,plain,(
% 1.70/0.64    $false | (~spl3_6 | ~spl3_8 | spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(trivial_inequality_removal,[],[f870])).
% 1.70/0.64  fof(f870,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0) | (~spl3_6 | ~spl3_8 | spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f802,f863])).
% 1.70/0.64  fof(f863,plain,(
% 1.70/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl3_6 | ~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f729,f862])).
% 1.70/0.64  fof(f862,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f850,f861])).
% 1.70/0.64  fof(f861,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(subsumption_resolution,[],[f848,f819])).
% 1.70/0.64  fof(f819,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f818,f224])).
% 1.70/0.64  fof(f224,plain,(
% 1.70/0.64    k1_xboole_0 = sK2 | ~spl3_12),
% 1.70/0.64    inference(avatar_component_clause,[],[f222])).
% 1.70/0.64  fof(f222,plain,(
% 1.70/0.64    spl3_12 <=> k1_xboole_0 = sK2),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.70/0.64  fof(f848,plain,(
% 1.70/0.64    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(resolution,[],[f817,f76])).
% 1.70/0.64  fof(f817,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f816,f224])).
% 1.70/0.64  fof(f850,plain,(
% 1.70/0.64    k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(resolution,[],[f817,f55])).
% 1.70/0.64  fof(f729,plain,(
% 1.70/0.64    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f123,f224])).
% 1.70/0.64  fof(f802,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k6_relat_1(k2_relat_1(k1_xboole_0)) | (~spl3_8 | spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f763,f148])).
% 1.70/0.64  fof(f763,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k6_relat_1(k2_relat_1(k1_xboole_0)) | (spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f762,f742])).
% 1.70/0.64  fof(f742,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_relat_1(k2_relat_1(k1_xboole_0)) | ~spl3_12),
% 1.70/0.64    inference(backward_demodulation,[],[f540,f224])).
% 1.70/0.64  fof(f762,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) | (spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f179,f224])).
% 1.70/0.64  fof(f179,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k5_relat_1(k2_funct_1(sK2),sK2) | spl3_10),
% 1.70/0.64    inference(avatar_component_clause,[],[f178])).
% 1.70/0.64  fof(f717,plain,(
% 1.70/0.64    spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_9 | spl3_13),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f716])).
% 1.70/0.64  fof(f716,plain,(
% 1.70/0.64    $false | (spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f715,f672])).
% 1.70/0.64  fof(f672,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2)) | (spl3_1 | ~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f622,f663])).
% 1.70/0.64  fof(f663,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f662,f660])).
% 1.70/0.64  fof(f660,plain,(
% 1.70/0.64    k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_6 | ~spl3_9)),
% 1.70/0.64    inference(forward_demodulation,[],[f649,f123])).
% 1.70/0.64  fof(f649,plain,(
% 1.70/0.64    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(resolution,[],[f620,f55])).
% 1.70/0.64  fof(f620,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~spl3_9),
% 1.70/0.64    inference(forward_demodulation,[],[f165,f152])).
% 1.70/0.64  fof(f662,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_9 | spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f661,f648])).
% 1.70/0.64  fof(f648,plain,(
% 1.70/0.64    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_9 | spl3_13)),
% 1.70/0.64    inference(superposition,[],[f227,f152])).
% 1.70/0.64  fof(f227,plain,(
% 1.70/0.64    k1_xboole_0 != k2_struct_0(sK0) | spl3_13),
% 1.70/0.64    inference(avatar_component_clause,[],[f226])).
% 1.70/0.64  fof(f661,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(subsumption_resolution,[],[f650,f619])).
% 1.70/0.64  fof(f619,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(forward_demodulation,[],[f161,f152])).
% 1.70/0.64  fof(f650,plain,(
% 1.70/0.64    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(resolution,[],[f620,f56])).
% 1.70/0.64  fof(f56,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.70/0.64    inference(cnf_transformation,[],[f38])).
% 1.70/0.64  fof(f622,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k1_relat_1(sK2),k2_struct_0(sK1),k2_struct_0(sK1),k1_relat_1(sK2),sK2,k2_funct_1(sK2)) | (spl3_1 | ~spl3_9)),
% 1.70/0.64    inference(forward_demodulation,[],[f170,f152])).
% 1.70/0.64  fof(f170,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | spl3_1),
% 1.70/0.64    inference(backward_demodulation,[],[f142,f169])).
% 1.70/0.64  fof(f142,plain,(
% 1.70/0.64    k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relat_1(sK2)) | spl3_1),
% 1.70/0.64    inference(backward_demodulation,[],[f98,f131])).
% 1.70/0.64  fof(f98,plain,(
% 1.70/0.64    k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_1),
% 1.70/0.64    inference(backward_demodulation,[],[f88,f93])).
% 1.70/0.64  fof(f88,plain,(
% 1.70/0.64    k1_partfun1(k2_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k2_struct_0(sK0),sK2,k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 1.70/0.64    inference(backward_demodulation,[],[f80,f87])).
% 1.70/0.64  fof(f715,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2)) | (~spl3_4 | ~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f714,f111])).
% 1.70/0.64  fof(f714,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2)) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f712,f41])).
% 1.70/0.64  fof(f712,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2),sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(resolution,[],[f681,f666])).
% 1.70/0.64  fof(f666,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f616,f663])).
% 1.70/0.64  fof(f616,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~spl3_9),
% 1.70/0.64    inference(forward_demodulation,[],[f95,f152])).
% 1.70/0.64  fof(f681,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k2_relat_1(sK2),k1_relat_1(sK2),X2,k2_funct_1(sK2)) | ~v1_funct_1(X2)) ) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f680,f663])).
% 1.70/0.64  fof(f680,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK1),k1_relat_1(sK2),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_9),
% 1.70/0.64    inference(subsumption_resolution,[],[f656,f157])).
% 1.70/0.64  fof(f656,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK1),k1_relat_1(sK2),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_9),
% 1.70/0.64    inference(resolution,[],[f620,f68])).
% 1.70/0.64  fof(f609,plain,(
% 1.70/0.64    spl3_1 | ~spl3_8 | ~spl3_13),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f608])).
% 1.70/0.64  fof(f608,plain,(
% 1.70/0.64    $false | (spl3_1 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(trivial_inequality_removal,[],[f607])).
% 1.70/0.64  fof(f607,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k6_relat_1(k1_xboole_0) | (spl3_1 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f606,f560])).
% 1.70/0.64  fof(f560,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relat_1(sK2) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f545,f556])).
% 1.70/0.64  fof(f556,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f542,f525])).
% 1.70/0.64  fof(f525,plain,(
% 1.70/0.64    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f512,f228])).
% 1.70/0.64  fof(f512,plain,(
% 1.70/0.64    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f96,f148])).
% 1.70/0.64  fof(f542,plain,(
% 1.70/0.64    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f526,f76])).
% 1.70/0.64  fof(f526,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f513,f228])).
% 1.70/0.64  fof(f513,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f95,f148])).
% 1.70/0.64  fof(f545,plain,(
% 1.70/0.64    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f526,f55])).
% 1.70/0.64  fof(f606,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_xboole_0) | (spl3_1 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f520,f605])).
% 1.70/0.64  fof(f605,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f599,f604])).
% 1.70/0.64  fof(f604,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f537,f560])).
% 1.70/0.64  fof(f537,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 1.70/0.64    inference(subsumption_resolution,[],[f536,f194])).
% 1.70/0.64  fof(f536,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f532,f41])).
% 1.70/0.64  fof(f532,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f45,f52])).
% 1.70/0.64  fof(f52,plain,(
% 1.70/0.64    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f22])).
% 1.70/0.64  fof(f599,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f597,f41])).
% 1.70/0.64  fof(f597,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f590,f526])).
% 1.70/0.64  fof(f590,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k1_xboole_0,k1_xboole_0,X2,k2_funct_1(sK2)) | ~v1_funct_1(X2)) ) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f579,f157])).
% 1.70/0.64  fof(f579,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(sK2)) = k1_partfun1(X0,X1,k1_xboole_0,k1_xboole_0,X2,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(resolution,[],[f522,f68])).
% 1.70/0.64  fof(f522,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f508,f228])).
% 1.70/0.64  fof(f508,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl3_8),
% 1.70/0.64    inference(forward_demodulation,[],[f165,f148])).
% 1.70/0.64  fof(f520,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK2)) | (spl3_1 | ~spl3_8 | ~spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f505,f228])).
% 1.70/0.64  fof(f505,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | (spl3_1 | ~spl3_8)),
% 1.70/0.64    inference(forward_demodulation,[],[f170,f148])).
% 1.70/0.64  fof(f498,plain,(
% 1.70/0.64    spl3_1 | ~spl3_4 | ~spl3_8 | ~spl3_12),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f497])).
% 1.70/0.64  fof(f497,plain,(
% 1.70/0.64    $false | (spl3_1 | ~spl3_4 | ~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(subsumption_resolution,[],[f496,f432])).
% 1.70/0.64  fof(f432,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(k1_xboole_0)) != k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0)) | (spl3_1 | ~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f409,f148])).
% 1.70/0.64  fof(f409,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(k1_xboole_0)) != k1_partfun1(k2_struct_0(sK0),k2_struct_0(sK1),k2_struct_0(sK1),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0)) | (spl3_1 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f170,f224])).
% 1.70/0.64  fof(f496,plain,(
% 1.70/0.64    k6_relat_1(k1_relat_1(k1_xboole_0)) = k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl3_4 | ~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f495,f400])).
% 1.70/0.64  fof(f400,plain,(
% 1.70/0.64    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_relat_1(k1_relat_1(k1_xboole_0)) | (~spl3_4 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f111,f224])).
% 1.70/0.64  fof(f495,plain,(
% 1.70/0.64    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(subsumption_resolution,[],[f493,f395])).
% 1.70/0.64  fof(f395,plain,(
% 1.70/0.64    v1_funct_1(k1_xboole_0) | ~spl3_12),
% 1.70/0.64    inference(backward_demodulation,[],[f41,f224])).
% 1.70/0.64  fof(f493,plain,(
% 1.70/0.64    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_partfun1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(resolution,[],[f479,f426])).
% 1.70/0.64  fof(f426,plain,(
% 1.70/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f398,f148])).
% 1.70/0.64  fof(f398,plain,(
% 1.70/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 1.70/0.64    inference(backward_demodulation,[],[f95,f224])).
% 1.70/0.64  fof(f479,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,k1_xboole_0,k2_struct_0(sK0),X2,k2_funct_1(k1_xboole_0)) = k5_relat_1(X2,k2_funct_1(k1_xboole_0)) | ~v1_funct_1(X2)) ) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(subsumption_resolution,[],[f468,f405])).
% 1.70/0.64  fof(f405,plain,(
% 1.70/0.64    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl3_12),
% 1.70/0.64    inference(backward_demodulation,[],[f157,f224])).
% 1.70/0.64  fof(f468,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k1_xboole_0,k2_struct_0(sK0),X2,k2_funct_1(k1_xboole_0)) = k5_relat_1(X2,k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(resolution,[],[f430,f68])).
% 1.70/0.64  fof(f430,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f407,f148])).
% 1.70/0.64  fof(f407,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_12),
% 1.70/0.64    inference(backward_demodulation,[],[f165,f224])).
% 1.70/0.64  fof(f487,plain,(
% 1.70/0.64    spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f486])).
% 1.70/0.64  fof(f486,plain,(
% 1.70/0.64    $false | (spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(subsumption_resolution,[],[f485,f438])).
% 1.70/0.64  fof(f438,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0) | (spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f435,f434])).
% 1.70/0.64  fof(f434,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k6_relat_1(k2_relat_1(k1_xboole_0)) | (~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f413,f148])).
% 1.70/0.64  fof(f413,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(k1_xboole_0)) | (~spl3_5 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f231,f224])).
% 1.70/0.64  fof(f231,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) = k6_relat_1(k2_relat_1(sK2)) | (~spl3_5 | ~spl3_10)),
% 1.70/0.64    inference(forward_demodulation,[],[f180,f117])).
% 1.70/0.64  fof(f117,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_5),
% 1.70/0.64    inference(avatar_component_clause,[],[f115])).
% 1.70/0.64  fof(f115,plain,(
% 1.70/0.64    spl3_5 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.70/0.64  fof(f435,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(k1_xboole_0)) != k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0) | (spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f414,f148])).
% 1.70/0.64  fof(f414,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(k1_xboole_0)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(k1_xboole_0),k1_xboole_0) | (spl3_2 | ~spl3_5 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f232,f224])).
% 1.70/0.64  fof(f232,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | (spl3_2 | ~spl3_5 | ~spl3_10)),
% 1.70/0.64    inference(backward_demodulation,[],[f171,f231])).
% 1.70/0.64  fof(f171,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | spl3_2),
% 1.70/0.64    inference(backward_demodulation,[],[f97,f169])).
% 1.70/0.64  fof(f97,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(k2_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK2) | spl3_2),
% 1.70/0.64    inference(backward_demodulation,[],[f89,f93])).
% 1.70/0.64  fof(f89,plain,(
% 1.70/0.64    k6_relat_1(k2_struct_0(sK1)) != k1_partfun1(u1_struct_0(sK1),k2_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) | spl3_2),
% 1.70/0.64    inference(backward_demodulation,[],[f86,f87])).
% 1.70/0.64  fof(f86,plain,(
% 1.70/0.64    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_struct_0(sK1)) | spl3_2),
% 1.70/0.64    inference(forward_demodulation,[],[f84,f44])).
% 1.70/0.64  fof(f485,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(forward_demodulation,[],[f484,f437])).
% 1.70/0.64  fof(f437,plain,(
% 1.70/0.64    k6_relat_1(k1_xboole_0) = k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f401,f434])).
% 1.70/0.64  fof(f401,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_relat_1(k2_relat_1(k1_xboole_0)) | (~spl3_5 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f117,f224])).
% 1.70/0.64  fof(f484,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(subsumption_resolution,[],[f482,f405])).
% 1.70/0.64  fof(f482,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_partfun1(k1_xboole_0,k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0,k2_funct_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(resolution,[],[f433,f430])).
% 1.70/0.64  fof(f433,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,k1_xboole_0) = k1_partfun1(X0,X1,k2_struct_0(sK0),k1_xboole_0,X2,k1_xboole_0) | ~v1_funct_1(X2)) ) | (~spl3_8 | ~spl3_12)),
% 1.70/0.64    inference(backward_demodulation,[],[f410,f148])).
% 1.70/0.64  fof(f410,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_struct_0(sK0),k2_struct_0(sK1),X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_12),
% 1.70/0.64    inference(backward_demodulation,[],[f172,f224])).
% 1.70/0.64  fof(f394,plain,(
% 1.70/0.64    spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_13),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f393])).
% 1.70/0.64  fof(f393,plain,(
% 1.70/0.64    $false | (spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f392,f287])).
% 1.70/0.64  fof(f287,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | (spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f243,f276])).
% 1.70/0.64  fof(f276,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f275,f273])).
% 1.70/0.64  fof(f273,plain,(
% 1.70/0.64    k2_relat_1(sK2) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_6 | ~spl3_9)),
% 1.70/0.64    inference(forward_demodulation,[],[f262,f123])).
% 1.70/0.64  fof(f262,plain,(
% 1.70/0.64    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(resolution,[],[f239,f55])).
% 1.70/0.64  fof(f239,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~spl3_9),
% 1.70/0.64    inference(backward_demodulation,[],[f165,f152])).
% 1.70/0.64  fof(f275,plain,(
% 1.70/0.64    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_9 | spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f274,f261])).
% 1.70/0.64  fof(f261,plain,(
% 1.70/0.64    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_9 | spl3_13)),
% 1.70/0.64    inference(superposition,[],[f227,f152])).
% 1.70/0.64  fof(f274,plain,(
% 1.70/0.64    k1_xboole_0 = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(subsumption_resolution,[],[f263,f238])).
% 1.70/0.64  fof(f238,plain,(
% 1.70/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(backward_demodulation,[],[f161,f152])).
% 1.70/0.64  fof(f263,plain,(
% 1.70/0.64    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_9),
% 1.70/0.64    inference(resolution,[],[f239,f56])).
% 1.70/0.64  fof(f243,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK1),k1_relat_1(sK2),k1_relat_1(sK2),k2_struct_0(sK1),k2_funct_1(sK2),sK2) | (spl3_2 | ~spl3_5 | ~spl3_9 | ~spl3_10)),
% 1.70/0.64    inference(backward_demodulation,[],[f232,f152])).
% 1.70/0.64  fof(f392,plain,(
% 1.70/0.64    k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | (~spl3_5 | ~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(forward_demodulation,[],[f391,f117])).
% 1.70/0.64  fof(f391,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(subsumption_resolution,[],[f389,f157])).
% 1.70/0.64  fof(f389,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(resolution,[],[f286,f283])).
% 1.70/0.64  fof(f283,plain,(
% 1.70/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f239,f276])).
% 1.70/0.64  fof(f286,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_relat_1(sK2),k2_relat_1(sK2),X2,sK2) | ~v1_funct_1(X2)) ) | (~spl3_6 | ~spl3_9 | spl3_13)),
% 1.70/0.64    inference(backward_demodulation,[],[f242,f276])).
% 1.70/0.64  fof(f242,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k1_relat_1(sK2),k2_struct_0(sK1),X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_9),
% 1.70/0.64    inference(backward_demodulation,[],[f172,f152])).
% 1.70/0.64  fof(f229,plain,(
% 1.70/0.64    spl3_12 | spl3_13 | ~spl3_8),
% 1.70/0.64    inference(avatar_split_clause,[],[f220,f146,f226,f222])).
% 1.70/0.64  fof(f220,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_8),
% 1.70/0.64    inference(subsumption_resolution,[],[f208,f198])).
% 1.70/0.64  fof(f198,plain,(
% 1.70/0.64    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_8),
% 1.70/0.64    inference(backward_demodulation,[],[f96,f148])).
% 1.70/0.64  fof(f208,plain,(
% 1.70/0.64    ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_8),
% 1.70/0.64    inference(resolution,[],[f197,f74])).
% 1.70/0.64  fof(f197,plain,(
% 1.70/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.70/0.64    inference(backward_demodulation,[],[f95,f148])).
% 1.70/0.64  fof(f193,plain,(
% 1.70/0.64    spl3_3),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f192])).
% 1.70/0.64  fof(f192,plain,(
% 1.70/0.64    $false | spl3_3),
% 1.70/0.64    inference(subsumption_resolution,[],[f191,f54])).
% 1.70/0.64  fof(f191,plain,(
% 1.70/0.64    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_3),
% 1.70/0.64    inference(subsumption_resolution,[],[f141,f107])).
% 1.70/0.64  fof(f107,plain,(
% 1.70/0.64    ~v1_relat_1(sK2) | spl3_3),
% 1.70/0.64    inference(avatar_component_clause,[],[f105])).
% 1.70/0.64  fof(f105,plain,(
% 1.70/0.64    spl3_3 <=> v1_relat_1(sK2)),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.70/0.64  fof(f190,plain,(
% 1.70/0.64    spl3_11 | spl3_8),
% 1.70/0.64    inference(avatar_split_clause,[],[f185,f146,f187])).
% 1.70/0.64  fof(f185,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0))),
% 1.70/0.64    inference(subsumption_resolution,[],[f184,f41])).
% 1.70/0.64  fof(f184,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f183,f96])).
% 1.70/0.64  fof(f183,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f182,f94])).
% 1.70/0.64  fof(f182,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f140,f45])).
% 1.70/0.64  fof(f140,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f71])).
% 1.70/0.64  fof(f71,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f66,f47])).
% 1.70/0.64  fof(f47,plain,(
% 1.70/0.64    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f8])).
% 1.70/0.64  fof(f8,axiom,(
% 1.70/0.64    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.70/0.64  fof(f66,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f31])).
% 1.70/0.64  fof(f31,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.70/0.64    inference(flattening,[],[f30])).
% 1.70/0.64  fof(f30,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.70/0.64    inference(ennf_transformation,[],[f10])).
% 1.70/0.64  fof(f10,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.70/0.64  fof(f181,plain,(
% 1.70/0.64    spl3_10 | spl3_8),
% 1.70/0.64    inference(avatar_split_clause,[],[f176,f146,f178])).
% 1.70/0.64  fof(f176,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f175,f41])).
% 1.70/0.64  fof(f175,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f174,f96])).
% 1.70/0.64  fof(f174,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f173,f94])).
% 1.70/0.64  fof(f173,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f139,f45])).
% 1.70/0.64  fof(f139,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k6_relat_1(k2_struct_0(sK1)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f70])).
% 1.70/0.64  fof(f70,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f67,f47])).
% 1.70/0.64  fof(f67,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f31])).
% 1.70/0.64  fof(f153,plain,(
% 1.70/0.64    spl3_8 | spl3_9),
% 1.70/0.64    inference(avatar_split_clause,[],[f144,f150,f146])).
% 1.70/0.64  fof(f144,plain,(
% 1.70/0.64    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 1.70/0.64    inference(forward_demodulation,[],[f143,f131])).
% 1.70/0.64  fof(f143,plain,(
% 1.70/0.64    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f132,f96])).
% 1.70/0.64  fof(f132,plain,(
% 1.70/0.64    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.70/0.64    inference(resolution,[],[f95,f56])).
% 1.70/0.64  fof(f124,plain,(
% 1.70/0.64    ~spl3_3 | spl3_6),
% 1.70/0.64    inference(avatar_split_clause,[],[f119,f121,f105])).
% 1.70/0.64  fof(f119,plain,(
% 1.70/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f101,f41])).
% 1.70/0.64  fof(f101,plain,(
% 1.70/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f45,f50])).
% 1.70/0.64  fof(f50,plain,(
% 1.70/0.64    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f20])).
% 1.70/0.64  fof(f20,plain,(
% 1.70/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.64    inference(flattening,[],[f19])).
% 1.70/0.64  fof(f19,plain,(
% 1.70/0.64    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.70/0.64    inference(ennf_transformation,[],[f3])).
% 1.70/0.64  fof(f3,axiom,(
% 1.70/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.70/0.64  fof(f118,plain,(
% 1.70/0.64    ~spl3_3 | spl3_5),
% 1.70/0.64    inference(avatar_split_clause,[],[f113,f115,f105])).
% 1.70/0.64  fof(f113,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f100,f41])).
% 1.70/0.64  fof(f100,plain,(
% 1.70/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f45,f53])).
% 1.70/0.64  fof(f112,plain,(
% 1.70/0.64    ~spl3_3 | spl3_4),
% 1.70/0.64    inference(avatar_split_clause,[],[f103,f109,f105])).
% 1.70/0.64  fof(f103,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(subsumption_resolution,[],[f99,f41])).
% 1.70/0.64  fof(f99,plain,(
% 1.70/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.70/0.64    inference(resolution,[],[f45,f52])).
% 1.70/0.64  fof(f85,plain,(
% 1.70/0.64    ~spl3_1 | ~spl3_2),
% 1.70/0.64    inference(avatar_split_clause,[],[f69,f82,f78])).
% 1.70/0.64  fof(f69,plain,(
% 1.70/0.64    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.70/0.64    inference(definition_unfolding,[],[f46,f47,f47])).
% 1.70/0.64  fof(f46,plain,(
% 1.70/0.64    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.70/0.64    inference(cnf_transformation,[],[f37])).
% 1.70/0.64  % SZS output end Proof for theBenchmark
% 1.70/0.64  % (9332)------------------------------
% 1.70/0.64  % (9332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (9332)Termination reason: Refutation
% 1.70/0.64  
% 1.70/0.64  % (9332)Memory used [KB]: 11129
% 1.70/0.64  % (9332)Time elapsed: 0.199 s
% 1.70/0.64  % (9332)------------------------------
% 1.70/0.64  % (9332)------------------------------
% 2.16/0.65  % (9323)Success in time 0.279 s
%------------------------------------------------------------------------------
