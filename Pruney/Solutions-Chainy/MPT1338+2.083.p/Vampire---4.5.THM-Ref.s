%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 918 expanded)
%              Number of leaves         :   23 ( 339 expanded)
%              Depth                    :   25
%              Number of atoms          :  509 (7604 expanded)
%              Number of equality atoms :  152 (2478 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f145,f213,f399,f415,f434,f493,f503])).

fof(f503,plain,
    ( ~ spl3_5
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl3_5
    | spl3_16 ),
    inference(subsumption_resolution,[],[f501,f98])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f97,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f97,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
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
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
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
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f501,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_16 ),
    inference(trivial_inequality_removal,[],[f500])).

fof(f500,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_16 ),
    inference(superposition,[],[f455,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f455,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_5
    | spl3_16 ),
    inference(subsumption_resolution,[],[f454,f98])).

fof(f454,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_16 ),
    inference(subsumption_resolution,[],[f453,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f453,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_16 ),
    inference(subsumption_resolution,[],[f452,f44])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f452,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_16 ),
    inference(superposition,[],[f451,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f451,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | spl3_16 ),
    inference(forward_demodulation,[],[f450,f299])).

fof(f299,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f276,f287])).

fof(f287,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f281,f42])).

fof(f281,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(superposition,[],[f141,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f141,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_5
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f276,plain,(
    k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f275,f40])).

fof(f275,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f274,f117])).

fof(f117,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f93,f109])).

fof(f109,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f107,f42])).

fof(f107,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f55,f43])).

fof(f43,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f93,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f39,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f41,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f274,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f273,f116])).

fof(f116,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f92,f109])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f84,f39])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f42,f47])).

fof(f273,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f272,f44])).

fof(f272,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f65,f115])).

fof(f115,plain,(
    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f91,f109])).

fof(f91,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f83,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f43,f47])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f450,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_16 ),
    inference(forward_demodulation,[],[f449,f109])).

fof(f449,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | spl3_16 ),
    inference(subsumption_resolution,[],[f448,f39])).

fof(f448,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | spl3_16 ),
    inference(superposition,[],[f433,f47])).

fof(f433,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl3_16
  <=> k1_relat_1(sK2) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f493,plain,
    ( ~ spl3_5
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f492])).

fof(f492,plain,
    ( $false
    | ~ spl3_5
    | spl3_15 ),
    inference(subsumption_resolution,[],[f491,f98])).

fof(f491,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_15 ),
    inference(trivial_inequality_removal,[],[f490])).

fof(f490,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_15 ),
    inference(superposition,[],[f442,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f442,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_5
    | spl3_15 ),
    inference(subsumption_resolution,[],[f441,f98])).

fof(f441,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_15 ),
    inference(subsumption_resolution,[],[f440,f40])).

fof(f440,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_15 ),
    inference(subsumption_resolution,[],[f439,f44])).

fof(f439,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_15 ),
    inference(superposition,[],[f438,f52])).

fof(f438,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | spl3_15 ),
    inference(forward_demodulation,[],[f437,f299])).

fof(f437,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_15 ),
    inference(forward_demodulation,[],[f436,f109])).

fof(f436,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | spl3_15 ),
    inference(subsumption_resolution,[],[f435,f39])).

fof(f435,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | spl3_15 ),
    inference(superposition,[],[f392,f47])).

fof(f392,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl3_15
  <=> k2_relat_1(sK2) = k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f434,plain,
    ( ~ spl3_14
    | ~ spl3_16
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f427,f140,f75,f432,f388])).

fof(f388,plain,
    ( spl3_14
  <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f75,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f427,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f425,f55])).

fof(f425,plain,
    ( k1_relat_1(sK2) != k2_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f424,f326])).

fof(f326,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f324,f37])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f324,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(superposition,[],[f287,f47])).

fof(f424,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f76,f287])).

fof(f76,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f415,plain,
    ( ~ spl3_5
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl3_5
    | spl3_14 ),
    inference(subsumption_resolution,[],[f413,f40])).

fof(f413,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_5
    | spl3_14 ),
    inference(subsumption_resolution,[],[f412,f288])).

fof(f288,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f41,f287])).

fof(f412,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | spl3_14 ),
    inference(subsumption_resolution,[],[f410,f289])).

fof(f289,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f42,f287])).

fof(f410,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | spl3_14 ),
    inference(resolution,[],[f389,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f389,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f388])).

fof(f399,plain,
    ( ~ spl3_15
    | ~ spl3_14
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f398,f140,f72,f388,f391])).

fof(f72,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f398,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f397,f287])).

fof(f397,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f128,f287])).

fof(f128,plain,
    ( k1_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_relat_1(sK2)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl3_1 ),
    inference(superposition,[],[f111,f54])).

fof(f111,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_relat_1(sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f73,f109])).

fof(f73,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f213,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f204,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f204,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f121,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f109,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f195,f39])).

fof(f195,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f144,f47])).

fof(f144,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_6
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f121,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f120,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f119,f39])).

fof(f119,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f51,f109])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f145,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f138,f143,f140])).

fof(f138,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f137,f41])).

fof(f137,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f77,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f75,f72])).

fof(f45,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (13348)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (13348)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (13366)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (13354)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (13364)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (13361)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (13347)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13350)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (13357)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (13352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (13346)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f77,f145,f213,f399,f415,f434,f493,f503])).
% 0.20/0.50  fof(f503,plain,(
% 0.20/0.50    ~spl3_5 | spl3_16),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f502])).
% 0.20/0.50  fof(f502,plain,(
% 0.20/0.50    $false | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f501,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f97,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 0.20/0.50    inference(resolution,[],[f50,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f34,f33,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f501,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f500])).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(superposition,[],[f455,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.50  fof(f455,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f454,f98])).
% 0.20/0.50  fof(f454,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f453,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f453,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f452,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f452,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(superposition,[],[f451,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.50  fof(f451,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (~spl3_5 | spl3_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f450,f299])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_5),
% 0.20/0.50    inference(backward_demodulation,[],[f276,f287])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f281,f42])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.20/0.50    inference(superposition,[],[f141,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl3_5 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f275,f40])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f274,f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f93,f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f42])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    inference(superposition,[],[f55,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f85,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f41,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f273,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.50    inference(backward_demodulation,[],[f92,f109])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f84,f39])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f42,f47])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f272,f44])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f271])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f65,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f91,f109])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f83,f39])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~l1_struct_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f43,f47])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  fof(f450,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_16),
% 0.20/0.50    inference(forward_demodulation,[],[f449,f109])).
% 0.20/0.50  fof(f449,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | spl3_16),
% 0.20/0.50    inference(subsumption_resolution,[],[f448,f39])).
% 0.20/0.50  fof(f448,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | spl3_16),
% 0.20/0.50    inference(superposition,[],[f433,f47])).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f432])).
% 0.20/0.50  fof(f432,plain,(
% 0.20/0.50    spl3_16 <=> k1_relat_1(sK2) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f493,plain,(
% 0.20/0.50    ~spl3_5 | spl3_15),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f492])).
% 0.20/0.50  fof(f492,plain,(
% 0.20/0.50    $false | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f491,f98])).
% 0.20/0.50  fof(f491,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f490])).
% 0.20/0.50  fof(f490,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(superposition,[],[f442,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f442,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f441,f98])).
% 0.20/0.50  fof(f441,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f440,f40])).
% 0.20/0.50  fof(f440,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f439,f44])).
% 0.20/0.50  fof(f439,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(superposition,[],[f438,f52])).
% 0.20/0.50  fof(f438,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | spl3_15)),
% 0.20/0.50    inference(forward_demodulation,[],[f437,f299])).
% 0.20/0.50  fof(f437,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_15),
% 0.20/0.50    inference(forward_demodulation,[],[f436,f109])).
% 0.20/0.50  fof(f436,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | spl3_15),
% 0.20/0.50    inference(subsumption_resolution,[],[f435,f39])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | spl3_15),
% 0.20/0.50    inference(superposition,[],[f392,f47])).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f391])).
% 0.20/0.50  fof(f391,plain,(
% 0.20/0.50    spl3_15 <=> k2_relat_1(sK2) = k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f434,plain,(
% 0.20/0.50    ~spl3_14 | ~spl3_16 | spl3_2 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f427,f140,f75,f432,f388])).
% 0.20/0.50  fof(f388,plain,(
% 0.20/0.50    spl3_14 <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | ~m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | (spl3_2 | ~spl3_5)),
% 0.20/0.50    inference(superposition,[],[f425,f55])).
% 0.20/0.50  fof(f425,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f424,f326])).
% 0.20/0.50  fof(f326,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f324,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~l1_struct_0(sK0) | ~spl3_5),
% 0.20/0.50    inference(superposition,[],[f287,f47])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f76,f287])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f415,plain,(
% 0.20/0.50    ~spl3_5 | spl3_14),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f414])).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    $false | (~spl3_5 | spl3_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f413,f40])).
% 0.20/0.50  fof(f413,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | (~spl3_5 | spl3_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f412,f288])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl3_5),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f287])).
% 0.20/0.50  fof(f412,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_5 | spl3_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f410,f289])).
% 0.20/0.50  fof(f289,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl3_5),
% 0.20/0.50    inference(backward_demodulation,[],[f42,f287])).
% 0.20/0.50  fof(f410,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | spl3_14),
% 0.20/0.50    inference(resolution,[],[f389,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    ~m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | spl3_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f388])).
% 0.20/0.50  fof(f399,plain,(
% 0.20/0.50    ~spl3_15 | ~spl3_14 | spl3_1 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f398,f140,f72,f388,f391])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f398,plain,(
% 0.20/0.50    ~m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f397,f287])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (spl3_1 | ~spl3_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f128,f287])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    k1_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_relat_1(sK2) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl3_1),
% 0.20/0.50    inference(superposition,[],[f111,f54])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_relat_1(sK2) | spl3_1),
% 0.20/0.50    inference(backward_demodulation,[],[f73,f109])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    ~spl3_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f212])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    $false | ~spl3_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f204,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl3_6),
% 0.20/0.50    inference(backward_demodulation,[],[f121,f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_6),
% 0.20/0.50    inference(backward_demodulation,[],[f109,f197])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f195,f39])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    k1_xboole_0 = k2_struct_0(sK1) | ~l1_struct_0(sK1) | ~spl3_6),
% 0.20/0.50    inference(superposition,[],[f144,f47])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    k1_xboole_0 = u1_struct_0(sK1) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl3_6 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f120,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f39])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f51,f109])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl3_5 | spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f138,f143,f140])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f41])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(resolution,[],[f56,f42])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f75,f72])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13348)------------------------------
% 0.20/0.50  % (13348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13348)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13348)Memory used [KB]: 10874
% 0.20/0.50  % (13348)Time elapsed: 0.071 s
% 0.20/0.50  % (13348)------------------------------
% 0.20/0.50  % (13348)------------------------------
% 0.20/0.50  % (13351)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (13343)Success in time 0.142 s
%------------------------------------------------------------------------------
