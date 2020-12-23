%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  180 (1068 expanded)
%              Number of leaves         :   32 ( 397 expanded)
%              Depth                    :   18
%              Number of atoms          :  585 (8720 expanded)
%              Number of equality atoms :  164 (2843 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f169,f173,f175,f273,f573,f596,f606,f871,f887,f906,f913,f1025,f1031,f1301])).

fof(f1301,plain,
    ( spl3_2
    | ~ spl3_15
    | ~ spl3_55
    | ~ spl3_82 ),
    inference(avatar_contradiction_clause,[],[f1300])).

fof(f1300,plain,
    ( $false
    | spl3_2
    | ~ spl3_15
    | ~ spl3_55
    | ~ spl3_82 ),
    inference(resolution,[],[f1299,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f1299,plain,
    ( ! [X0] : ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl3_2
    | ~ spl3_15
    | ~ spl3_55
    | ~ spl3_82 ),
    inference(subsumption_resolution,[],[f1297,f1110])).

fof(f1110,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_2
    | ~ spl3_15
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f1109,f156])).

fof(f156,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_15
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1109,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f1108,f982])).

fof(f982,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f981,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f981,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f980,f497])).

fof(f497,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f441,f310])).

fof(f310,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f303,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f303,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f50,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f50,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f441,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f376,f106])).

fof(f106,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f46,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f46,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f376,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f48,f85])).

fof(f85,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f44,f67])).

fof(f44,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f980,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f971,f564])).

fof(f564,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f375,f498])).

fof(f498,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f106,f310])).

fof(f375,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f49,f85])).

fof(f971,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_55 ),
    inference(superposition,[],[f57,f550])).

fof(f550,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl3_55
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f1108,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | spl3_2
    | ~ spl3_55 ),
    inference(superposition,[],[f1034,f64])).

fof(f1034,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f1033,f550])).

fof(f1033,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1032,f85])).

fof(f1032,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f82,f498])).

fof(f82,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1297,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) )
    | ~ spl3_82 ),
    inference(resolution,[],[f1240,f69])).

fof(f69,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1240,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0)
        | k1_relat_1(sK2) = X0
        | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_82 ),
    inference(resolution,[],[f904,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f904,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)
        | k1_relat_1(sK2) = X0
        | ~ v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0) )
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f903])).

fof(f903,plain,
    ( spl3_82
  <=> ! [X0] :
        ( k1_relat_1(sK2) = X0
        | ~ v4_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)
        | ~ v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f1031,plain,
    ( spl3_1
    | ~ spl3_14
    | ~ spl3_55 ),
    inference(avatar_contradiction_clause,[],[f1030])).

fof(f1030,plain,
    ( $false
    | spl3_1
    | ~ spl3_14
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f982,f995])).

fof(f995,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | spl3_1
    | ~ spl3_14
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f994,f151])).

fof(f151,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_14
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f994,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | spl3_1
    | ~ spl3_55 ),
    inference(superposition,[],[f968,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f968,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_55 ),
    inference(backward_demodulation,[],[f666,f550])).

fof(f666,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f665,f310])).

fof(f665,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f372,f498])).

fof(f372,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f78,f85])).

fof(f78,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1025,plain,(
    spl3_56 ),
    inference(avatar_contradiction_clause,[],[f1024])).

fof(f1024,plain,
    ( $false
    | spl3_56 ),
    inference(subsumption_resolution,[],[f595,f639])).

fof(f639,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f638,f310])).

fof(f638,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f373,f498])).

fof(f373,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f50,f85])).

fof(f595,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | spl3_56 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl3_56
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f913,plain,
    ( ~ spl3_36
    | ~ spl3_75
    | spl3_79 ),
    inference(avatar_contradiction_clause,[],[f912])).

fof(f912,plain,
    ( $false
    | ~ spl3_36
    | ~ spl3_75
    | spl3_79 ),
    inference(subsumption_resolution,[],[f910,f891])).

fof(f891,plain,
    ( ~ v1_relat_1(k6_partfun1(k2_struct_0(sK0)))
    | spl3_79 ),
    inference(avatar_component_clause,[],[f889])).

fof(f889,plain,
    ( spl3_79
  <=> v1_relat_1(k6_partfun1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f910,plain,
    ( v1_relat_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_36
    | ~ spl3_75 ),
    inference(forward_demodulation,[],[f776,f410])).

fof(f410,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl3_36
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f776,plain,
    ( v1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl3_75
  <=> v1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f906,plain,
    ( ~ spl3_79
    | spl3_82
    | ~ spl3_12
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f849,f408,f139,f903,f889])).

fof(f139,plain,
    ( spl3_12
  <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f849,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) = X0
        | ~ v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0)
        | ~ v4_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)
        | ~ v1_relat_1(k6_partfun1(k2_struct_0(sK0))) )
    | ~ spl3_12
    | ~ spl3_36 ),
    inference(superposition,[],[f833,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f833,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_12
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f141,f410])).

fof(f141,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f887,plain,
    ( ~ spl3_36
    | spl3_75 ),
    inference(avatar_contradiction_clause,[],[f886])).

fof(f886,plain,
    ( $false
    | ~ spl3_36
    | spl3_75 ),
    inference(resolution,[],[f848,f70])).

fof(f848,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl3_36
    | spl3_75 ),
    inference(resolution,[],[f832,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f832,plain,
    ( ~ v1_relat_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_36
    | spl3_75 ),
    inference(backward_demodulation,[],[f777,f410])).

fof(f777,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | spl3_75 ),
    inference(avatar_component_clause,[],[f775])).

fof(f871,plain,
    ( spl3_18
    | ~ spl3_50 ),
    inference(avatar_contradiction_clause,[],[f870])).

fof(f870,plain,
    ( $false
    | spl3_18
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f516,f578])).

fof(f578,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_18 ),
    inference(superposition,[],[f577,f310])).

fof(f577,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_18 ),
    inference(subsumption_resolution,[],[f576,f46])).

fof(f576,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | spl3_18 ),
    inference(superposition,[],[f196,f67])).

fof(f196,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_18
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f516,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl3_50
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f606,plain,
    ( ~ spl3_56
    | spl3_50
    | spl3_36 ),
    inference(avatar_split_clause,[],[f605,f408,f514,f593])).

fof(f605,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f604,f47])).

fof(f604,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f603,f497])).

fof(f603,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f584,f51])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f584,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f564,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f596,plain,
    ( ~ spl3_56
    | spl3_55 ),
    inference(avatar_split_clause,[],[f591,f548,f593])).

fof(f591,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f590,f47])).

fof(f590,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f589,f497])).

fof(f589,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f580,f51])).

fof(f580,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f564,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
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
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f573,plain,(
    ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f571,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f571,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f570,f46])).

fof(f570,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f567,f72])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f567,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_18 ),
    inference(superposition,[],[f71,f197])).

fof(f197,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f273,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_11 ),
    inference(subsumption_resolution,[],[f250,f137])).

fof(f137,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f250,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f68])).

fof(f175,plain,
    ( ~ spl3_11
    | spl3_15 ),
    inference(avatar_split_clause,[],[f174,f154,f135])).

fof(f174,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f164,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f173,plain,
    ( ~ spl3_11
    | spl3_14 ),
    inference(avatar_split_clause,[],[f172,f149,f135])).

fof(f172,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f47])).

fof(f163,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f169,plain,
    ( ~ spl3_11
    | spl3_12 ),
    inference(avatar_split_clause,[],[f168,f139,f135])).

fof(f168,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f47])).

fof(f161,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f83,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f80,f76])).

fof(f52,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:52:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (21576)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.45  % (21576)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f1302,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f83,f169,f173,f175,f273,f573,f596,f606,f871,f887,f906,f913,f1025,f1031,f1301])).
% 0.22/0.45  fof(f1301,plain,(
% 0.22/0.45    spl3_2 | ~spl3_15 | ~spl3_55 | ~spl3_82),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f1300])).
% 0.22/0.45  fof(f1300,plain,(
% 0.22/0.45    $false | (spl3_2 | ~spl3_15 | ~spl3_55 | ~spl3_82)),
% 0.22/0.45    inference(resolution,[],[f1299,f70])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.45  fof(f1299,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | (spl3_2 | ~spl3_15 | ~spl3_55 | ~spl3_82)),
% 0.22/0.45    inference(subsumption_resolution,[],[f1297,f1110])).
% 0.22/0.45  fof(f1110,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k1_relat_1(sK2) | (spl3_2 | ~spl3_15 | ~spl3_55)),
% 0.22/0.45    inference(forward_demodulation,[],[f1109,f156])).
% 0.22/0.45  fof(f156,plain,(
% 0.22/0.45    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f154])).
% 0.22/0.45  fof(f154,plain,(
% 0.22/0.45    spl3_15 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.45  fof(f1109,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | (spl3_2 | ~spl3_55)),
% 0.22/0.45    inference(subsumption_resolution,[],[f1108,f982])).
% 0.22/0.45  fof(f982,plain,(
% 0.22/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_55),
% 0.22/0.45    inference(subsumption_resolution,[],[f981,f47])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    v1_funct_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f41,f40,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.45    inference(negated_conjecture,[],[f15])).
% 0.22/0.45  fof(f15,conjecture,(
% 0.22/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.45  fof(f981,plain,(
% 0.22/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~spl3_55),
% 0.22/0.45    inference(subsumption_resolution,[],[f980,f497])).
% 0.22/0.45  fof(f497,plain,(
% 0.22/0.45    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.45    inference(backward_demodulation,[],[f441,f310])).
% 0.22/0.45  fof(f310,plain,(
% 0.22/0.45    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.45    inference(subsumption_resolution,[],[f303,f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.45    inference(cnf_transformation,[],[f42])).
% 0.22/0.45  fof(f303,plain,(
% 0.22/0.45    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.45    inference(superposition,[],[f50,f64])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f42])).
% 0.22/0.45  fof(f441,plain,(
% 0.22/0.45    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.45    inference(backward_demodulation,[],[f376,f106])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.45    inference(resolution,[],[f46,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    l1_struct_0(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f42])).
% 0.22/0.45  fof(f376,plain,(
% 0.22/0.45    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.45    inference(backward_demodulation,[],[f48,f85])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f44,f67])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    l1_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f42])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f42])).
% 0.22/0.45  fof(f980,plain,(
% 0.22/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_55),
% 0.22/0.45    inference(subsumption_resolution,[],[f971,f564])).
% 0.22/0.45  fof(f564,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.45    inference(forward_demodulation,[],[f375,f498])).
% 0.22/0.45  fof(f498,plain,(
% 0.22/0.45    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.45    inference(backward_demodulation,[],[f106,f310])).
% 0.22/0.45  fof(f375,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.45    inference(backward_demodulation,[],[f49,f85])).
% 0.22/0.45  fof(f971,plain,(
% 0.22/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_55),
% 0.22/0.45    inference(superposition,[],[f57,f550])).
% 0.22/0.45  fof(f550,plain,(
% 0.22/0.45    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_55),
% 0.22/0.45    inference(avatar_component_clause,[],[f548])).
% 0.22/0.45  fof(f548,plain,(
% 0.22/0.45    spl3_55 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.45    inference(flattening,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.45  fof(f1108,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (spl3_2 | ~spl3_55)),
% 0.22/0.45    inference(superposition,[],[f1034,f64])).
% 0.22/0.45  fof(f1034,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_2 | ~spl3_55)),
% 0.22/0.45    inference(forward_demodulation,[],[f1033,f550])).
% 0.22/0.45  fof(f1033,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_2),
% 0.22/0.45    inference(forward_demodulation,[],[f1032,f85])).
% 0.22/0.45  fof(f1032,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_2),
% 0.22/0.45    inference(forward_demodulation,[],[f82,f498])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f80])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f1297,plain,(
% 0.22/0.45    ( ! [X0] : (k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_82),
% 0.22/0.45    inference(resolution,[],[f1240,f69])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f1240,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0) | k1_relat_1(sK2) = X0 | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_82),
% 0.22/0.45    inference(resolution,[],[f904,f73])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.45    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.45  fof(f904,plain,(
% 0.22/0.45    ( ! [X0] : (~v4_relat_1(k6_partfun1(k2_struct_0(sK0)),X0) | k1_relat_1(sK2) = X0 | ~v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0)) ) | ~spl3_82),
% 0.22/0.45    inference(avatar_component_clause,[],[f903])).
% 0.22/0.45  fof(f903,plain,(
% 0.22/0.45    spl3_82 <=> ! [X0] : (k1_relat_1(sK2) = X0 | ~v4_relat_1(k6_partfun1(k2_struct_0(sK0)),X0) | ~v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.22/0.45  fof(f1031,plain,(
% 0.22/0.45    spl3_1 | ~spl3_14 | ~spl3_55),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f1030])).
% 0.22/0.45  fof(f1030,plain,(
% 0.22/0.45    $false | (spl3_1 | ~spl3_14 | ~spl3_55)),
% 0.22/0.45    inference(subsumption_resolution,[],[f982,f995])).
% 0.22/0.45  fof(f995,plain,(
% 0.22/0.45    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (spl3_1 | ~spl3_14 | ~spl3_55)),
% 0.22/0.45    inference(subsumption_resolution,[],[f994,f151])).
% 0.22/0.45  fof(f151,plain,(
% 0.22/0.45    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f149])).
% 0.22/0.45  fof(f149,plain,(
% 0.22/0.45    spl3_14 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.45  fof(f994,plain,(
% 0.22/0.45    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (spl3_1 | ~spl3_55)),
% 0.22/0.45    inference(superposition,[],[f968,f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.45  fof(f968,plain,(
% 0.22/0.45    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_1 | ~spl3_55)),
% 0.22/0.45    inference(backward_demodulation,[],[f666,f550])).
% 0.22/0.45  fof(f666,plain,(
% 0.22/0.45    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_1),
% 0.22/0.45    inference(forward_demodulation,[],[f665,f310])).
% 0.22/0.45  fof(f665,plain,(
% 0.22/0.45    k2_struct_0(sK1) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_1),
% 0.22/0.45    inference(forward_demodulation,[],[f372,f498])).
% 0.22/0.45  fof(f372,plain,(
% 0.22/0.45    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.45    inference(backward_demodulation,[],[f78,f85])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f1025,plain,(
% 0.22/0.45    spl3_56),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f1024])).
% 0.22/0.45  fof(f1024,plain,(
% 0.22/0.45    $false | spl3_56),
% 0.22/0.45    inference(subsumption_resolution,[],[f595,f639])).
% 0.22/0.45  fof(f639,plain,(
% 0.22/0.45    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.45    inference(forward_demodulation,[],[f638,f310])).
% 0.22/0.45  fof(f638,plain,(
% 0.22/0.45    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.45    inference(forward_demodulation,[],[f373,f498])).
% 0.22/0.45  fof(f373,plain,(
% 0.22/0.45    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.45    inference(backward_demodulation,[],[f50,f85])).
% 0.22/0.45  fof(f595,plain,(
% 0.22/0.45    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | spl3_56),
% 0.22/0.45    inference(avatar_component_clause,[],[f593])).
% 0.22/0.45  fof(f593,plain,(
% 0.22/0.45    spl3_56 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.45  fof(f913,plain,(
% 0.22/0.45    ~spl3_36 | ~spl3_75 | spl3_79),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f912])).
% 0.22/0.45  fof(f912,plain,(
% 0.22/0.45    $false | (~spl3_36 | ~spl3_75 | spl3_79)),
% 0.22/0.45    inference(subsumption_resolution,[],[f910,f891])).
% 0.22/0.45  fof(f891,plain,(
% 0.22/0.45    ~v1_relat_1(k6_partfun1(k2_struct_0(sK0))) | spl3_79),
% 0.22/0.45    inference(avatar_component_clause,[],[f889])).
% 0.22/0.45  fof(f889,plain,(
% 0.22/0.45    spl3_79 <=> v1_relat_1(k6_partfun1(k2_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 0.22/0.45  fof(f910,plain,(
% 0.22/0.45    v1_relat_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_36 | ~spl3_75)),
% 0.22/0.45    inference(forward_demodulation,[],[f776,f410])).
% 0.22/0.46  fof(f410,plain,(
% 0.22/0.46    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | ~spl3_36),
% 0.22/0.46    inference(avatar_component_clause,[],[f408])).
% 0.22/0.46  fof(f408,plain,(
% 0.22/0.46    spl3_36 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.46  fof(f776,plain,(
% 0.22/0.46    v1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl3_75),
% 0.22/0.46    inference(avatar_component_clause,[],[f775])).
% 0.22/0.46  fof(f775,plain,(
% 0.22/0.46    spl3_75 <=> v1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.22/0.46  fof(f906,plain,(
% 0.22/0.46    ~spl3_79 | spl3_82 | ~spl3_12 | ~spl3_36),
% 0.22/0.46    inference(avatar_split_clause,[],[f849,f408,f139,f903,f889])).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    spl3_12 <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.46  fof(f849,plain,(
% 0.22/0.46    ( ! [X0] : (k1_relat_1(sK2) = X0 | ~v1_partfun1(k6_partfun1(k2_struct_0(sK0)),X0) | ~v4_relat_1(k6_partfun1(k2_struct_0(sK0)),X0) | ~v1_relat_1(k6_partfun1(k2_struct_0(sK0)))) ) | (~spl3_12 | ~spl3_36)),
% 0.22/0.46    inference(superposition,[],[f833,f65])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f43])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.46  fof(f833,plain,(
% 0.22/0.46    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_12 | ~spl3_36)),
% 0.22/0.46    inference(backward_demodulation,[],[f141,f410])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl3_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f139])).
% 0.22/0.46  fof(f887,plain,(
% 0.22/0.46    ~spl3_36 | spl3_75),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f886])).
% 0.22/0.46  fof(f886,plain,(
% 0.22/0.46    $false | (~spl3_36 | spl3_75)),
% 0.22/0.46    inference(resolution,[],[f848,f70])).
% 0.22/0.46  fof(f848,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl3_36 | spl3_75)),
% 0.22/0.46    inference(resolution,[],[f832,f68])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.46  fof(f832,plain,(
% 0.22/0.46    ~v1_relat_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_36 | spl3_75)),
% 0.22/0.46    inference(backward_demodulation,[],[f777,f410])).
% 0.22/0.46  fof(f777,plain,(
% 0.22/0.46    ~v1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | spl3_75),
% 0.22/0.46    inference(avatar_component_clause,[],[f775])).
% 0.22/0.46  fof(f871,plain,(
% 0.22/0.46    spl3_18 | ~spl3_50),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f870])).
% 0.22/0.46  fof(f870,plain,(
% 0.22/0.46    $false | (spl3_18 | ~spl3_50)),
% 0.22/0.46    inference(subsumption_resolution,[],[f516,f578])).
% 0.22/0.46  fof(f578,plain,(
% 0.22/0.46    k1_xboole_0 != k2_relat_1(sK2) | spl3_18),
% 0.22/0.46    inference(superposition,[],[f577,f310])).
% 0.22/0.46  fof(f577,plain,(
% 0.22/0.46    k1_xboole_0 != k2_struct_0(sK1) | spl3_18),
% 0.22/0.46    inference(subsumption_resolution,[],[f576,f46])).
% 0.22/0.46  fof(f576,plain,(
% 0.22/0.46    k1_xboole_0 != k2_struct_0(sK1) | ~l1_struct_0(sK1) | spl3_18),
% 0.22/0.46    inference(superposition,[],[f196,f67])).
% 0.22/0.46  fof(f196,plain,(
% 0.22/0.46    k1_xboole_0 != u1_struct_0(sK1) | spl3_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f195])).
% 0.22/0.46  fof(f195,plain,(
% 0.22/0.46    spl3_18 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.46  fof(f516,plain,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_50),
% 0.22/0.46    inference(avatar_component_clause,[],[f514])).
% 0.22/0.46  fof(f514,plain,(
% 0.22/0.46    spl3_50 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.46  fof(f606,plain,(
% 0.22/0.46    ~spl3_56 | spl3_50 | spl3_36),
% 0.22/0.46    inference(avatar_split_clause,[],[f605,f408,f514,f593])).
% 0.22/0.46  fof(f605,plain,(
% 0.22/0.46    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f604,f47])).
% 0.22/0.46  fof(f604,plain,(
% 0.22/0.46    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f603,f497])).
% 0.22/0.46  fof(f603,plain,(
% 0.22/0.46    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f584,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    v2_funct_1(sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f42])).
% 0.22/0.46  fof(f584,plain,(
% 0.22/0.46    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.46    inference(resolution,[],[f564,f58])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.46    inference(flattening,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.46  fof(f596,plain,(
% 0.22/0.46    ~spl3_56 | spl3_55),
% 0.22/0.46    inference(avatar_split_clause,[],[f591,f548,f593])).
% 0.22/0.46  fof(f591,plain,(
% 0.22/0.46    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f590,f47])).
% 0.22/0.46  fof(f590,plain,(
% 0.22/0.46    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f589,f497])).
% 0.22/0.46  fof(f589,plain,(
% 0.22/0.46    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f580,f51])).
% 0.22/0.46  fof(f580,plain,(
% 0.22/0.46    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.46    inference(resolution,[],[f564,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.46    inference(flattening,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.46  fof(f573,plain,(
% 0.22/0.46    ~spl3_18),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f572])).
% 0.22/0.46  fof(f572,plain,(
% 0.22/0.46    $false | ~spl3_18),
% 0.22/0.46    inference(subsumption_resolution,[],[f571,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ~v2_struct_0(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f42])).
% 0.22/0.46  fof(f571,plain,(
% 0.22/0.46    v2_struct_0(sK1) | ~spl3_18),
% 0.22/0.46    inference(subsumption_resolution,[],[f570,f46])).
% 0.22/0.46  fof(f570,plain,(
% 0.22/0.46    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_18),
% 0.22/0.46    inference(subsumption_resolution,[],[f567,f72])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  fof(f567,plain,(
% 0.22/0.46    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_18),
% 0.22/0.46    inference(superposition,[],[f71,f197])).
% 0.22/0.46  fof(f197,plain,(
% 0.22/0.46    k1_xboole_0 = u1_struct_0(sK1) | ~spl3_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f195])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.46  fof(f273,plain,(
% 0.22/0.46    spl3_11),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f272])).
% 0.22/0.46  fof(f272,plain,(
% 0.22/0.46    $false | spl3_11),
% 0.22/0.46    inference(subsumption_resolution,[],[f250,f137])).
% 0.22/0.46  fof(f137,plain,(
% 0.22/0.46    ~v1_relat_1(sK2) | spl3_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f135])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl3_11 <=> v1_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.46  fof(f250,plain,(
% 0.22/0.46    v1_relat_1(sK2)),
% 0.22/0.46    inference(resolution,[],[f49,f68])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    ~spl3_11 | spl3_15),
% 0.22/0.46    inference(avatar_split_clause,[],[f174,f154,f135])).
% 0.22/0.46  fof(f174,plain,(
% 0.22/0.46    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f164,f47])).
% 0.22/0.46  fof(f164,plain,(
% 0.22/0.46    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.46    inference(resolution,[],[f51,f63])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.46  fof(f173,plain,(
% 0.22/0.46    ~spl3_11 | spl3_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f172,f149,f135])).
% 0.22/0.46  fof(f172,plain,(
% 0.22/0.46    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f163,f47])).
% 0.22/0.46  fof(f163,plain,(
% 0.22/0.46    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.46    inference(resolution,[],[f51,f62])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f30])).
% 0.22/0.46  fof(f169,plain,(
% 0.22/0.46    ~spl3_11 | spl3_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f168,f139,f135])).
% 0.22/0.46  fof(f168,plain,(
% 0.22/0.46    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.46    inference(subsumption_resolution,[],[f161,f47])).
% 0.22/0.46  fof(f161,plain,(
% 0.22/0.46    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.46    inference(resolution,[],[f51,f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    ~spl3_1 | ~spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f52,f80,f76])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.46    inference(cnf_transformation,[],[f42])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (21576)------------------------------
% 0.22/0.46  % (21576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (21576)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (21576)Memory used [KB]: 6652
% 0.22/0.46  % (21576)Time elapsed: 0.046 s
% 0.22/0.46  % (21576)------------------------------
% 0.22/0.46  % (21576)------------------------------
% 0.22/0.46  % (21556)Success in time 0.095 s
%------------------------------------------------------------------------------
