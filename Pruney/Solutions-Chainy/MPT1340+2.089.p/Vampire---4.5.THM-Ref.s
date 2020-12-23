%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  243 (1860 expanded)
%              Number of leaves         :   36 ( 681 expanded)
%              Depth                    :   18
%              Number of atoms          :  857 (13770 expanded)
%              Number of equality atoms :  139 (1949 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f348,f569,f629,f653,f657,f719,f822,f1149,f1209,f1345,f1513,f1716,f1818,f2359])).

fof(f2359,plain,
    ( ~ spl9_47
    | ~ spl9_48
    | spl9_49
    | ~ spl9_54
    | ~ spl9_55
    | ~ spl9_56 ),
    inference(avatar_contradiction_clause,[],[f2358])).

fof(f2358,plain,
    ( $false
    | ~ spl9_47
    | ~ spl9_48
    | spl9_49
    | ~ spl9_54
    | ~ spl9_55
    | ~ spl9_56 ),
    inference(subsumption_resolution,[],[f2357,f1848])).

fof(f1848,plain,
    ( sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_54
    | ~ spl9_55
    | ~ spl9_56 ),
    inference(subsumption_resolution,[],[f1847,f1486])).

fof(f1486,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f1485])).

fof(f1485,plain,
    ( spl9_54
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f1847,plain,
    ( sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_55
    | ~ spl9_56 ),
    inference(subsumption_resolution,[],[f1836,f1490])).

fof(f1490,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6))
    | ~ spl9_55 ),
    inference(avatar_component_clause,[],[f1489])).

fof(f1489,plain,
    ( spl9_55
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f1836,plain,
    ( sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_56 ),
    inference(resolution,[],[f1494,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f1494,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6))))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1493,plain,
    ( spl9_56
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f2357,plain,
    ( ~ sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_47
    | ~ spl9_48
    | spl9_49 ),
    inference(subsumption_resolution,[],[f2356,f1207])).

fof(f1207,plain,
    ( k1_xboole_0 != u1_struct_0(sK6)
    | spl9_49 ),
    inference(avatar_component_clause,[],[f1206])).

fof(f1206,plain,
    ( spl9_49
  <=> k1_xboole_0 = u1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f2356,plain,
    ( k1_xboole_0 = u1_struct_0(sK6)
    | ~ sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_47
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f2328,f1389])).

fof(f1389,plain,
    ( r2_funct_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl9_47
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1388,f1218])).

fof(f1218,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl9_47
    | ~ spl9_48 ),
    inference(backward_demodulation,[],[f1160,f1204])).

fof(f1204,plain,
    ( k1_xboole_0 = sK8
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1202,plain,
    ( spl9_48
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f1160,plain,
    ( k1_xboole_0 = k2_relat_1(sK8)
    | ~ spl9_47 ),
    inference(resolution,[],[f1114,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1114,plain,
    ( sP1(u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1112,plain,
    ( spl9_47
  <=> sP1(u1_struct_0(sK6),k2_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f1388,plain,
    ( r2_funct_2(u1_struct_0(sK6),k2_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f297,f1204])).

fof(f297,plain,(
    r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8) ),
    inference(subsumption_resolution,[],[f296,f67])).

fof(f67,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),sK8)
    & v2_funct_1(sK8)
    & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_struct_0(sK7)
    & ~ v2_struct_0(sK7)
    & l1_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f18,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
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
              ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X2) = k2_struct_0(sK7)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
          & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7))
          & v1_funct_1(X2) )
      & l1_struct_0(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X2) = k2_struct_0(sK7)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
        & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),sK8)
      & v2_funct_1(sK8)
      & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
      & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f296,plain,
    ( r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8)
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f288,f209])).

fof(f209,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) ),
    inference(backward_demodulation,[],[f126,f196])).

fof(f196,plain,(
    k2_struct_0(sK7) = k2_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f188,f69])).

fof(f69,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f188,plain,
    ( k2_struct_0(sK7) = k2_relat_1(sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(superposition,[],[f85,f70])).

fof(f70,plain,(
    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f126,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),k2_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f118,f66])).

fof(f66,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f118,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),k2_struct_0(sK7))
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f68,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f68,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f54])).

fof(f288,plain,
    ( r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[],[f110,f208])).

fof(f208,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) ),
    inference(backward_demodulation,[],[f125,f196])).

fof(f125,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK7)))) ),
    inference(subsumption_resolution,[],[f117,f66])).

fof(f117,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK7))))
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f69,f73])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f2328,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK6)
    | ~ sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | ~ spl9_47
    | ~ spl9_48 ),
    inference(superposition,[],[f1471,f727])).

fof(f727,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_tops_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | ~ sP4(k1_xboole_0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f725,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f725,plain,(
    ! [X0,X1] :
      ( ~ sP4(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = k2_tops_2(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f223,f107])).

fof(f107,plain,(
    ! [X2,X0] :
      ( ~ sP3(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( sP3(k2_tops_2(X0,X1,X2),X0,X1)
      | ~ sP4(X0,X1,X2) ) ),
    inference(resolution,[],[f96,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f32,f45,f44,f43])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1471,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k1_xboole_0,k2_tops_2(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl9_47
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1470,f1218])).

fof(f1470,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f206,f1204])).

fof(f206,plain,(
    ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8)),sK8) ),
    inference(backward_demodulation,[],[f123,f196])).

fof(f123,plain,(
    ~ r2_funct_2(u1_struct_0(sK6),k2_struct_0(sK7),k2_tops_2(k2_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_struct_0(sK7),sK8)),sK8) ),
    inference(subsumption_resolution,[],[f115,f66])).

fof(f115,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_struct_0(sK7),k2_tops_2(k2_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_struct_0(sK7),sK8)),sK8)
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f72,f73])).

fof(f72,plain,(
    ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f1818,plain,
    ( ~ spl9_47
    | ~ spl9_48
    | spl9_56 ),
    inference(avatar_contradiction_clause,[],[f1817])).

fof(f1817,plain,
    ( $false
    | ~ spl9_47
    | ~ spl9_48
    | spl9_56 ),
    inference(subsumption_resolution,[],[f1813,f1224])).

fof(f1224,plain,
    ( sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)
    | ~ spl9_47
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1173,f1204])).

fof(f1173,plain,
    ( sP4(u1_struct_0(sK6),k1_xboole_0,sK8)
    | ~ spl9_47 ),
    inference(backward_demodulation,[],[f254,f1160])).

fof(f254,plain,(
    sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8) ),
    inference(subsumption_resolution,[],[f253,f67])).

fof(f253,plain,
    ( sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f245,f209])).

fof(f245,plain,
    ( sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[],[f97,f208])).

fof(f1813,plain,
    ( ~ sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)
    | spl9_56 ),
    inference(resolution,[],[f1495,f96])).

fof(f1495,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6))))
    | spl9_56 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1716,plain,
    ( ~ spl9_47
    | ~ spl9_48
    | spl9_55 ),
    inference(avatar_contradiction_clause,[],[f1715])).

fof(f1715,plain,
    ( $false
    | ~ spl9_47
    | ~ spl9_48
    | spl9_55 ),
    inference(subsumption_resolution,[],[f1712,f1224])).

fof(f1712,plain,
    ( ~ sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)
    | spl9_55 ),
    inference(resolution,[],[f1491,f95])).

fof(f1491,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6))
    | spl9_55 ),
    inference(avatar_component_clause,[],[f1489])).

fof(f1513,plain,
    ( ~ spl9_47
    | ~ spl9_48
    | spl9_54 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | ~ spl9_47
    | ~ spl9_48
    | spl9_54 ),
    inference(subsumption_resolution,[],[f1509,f1224])).

fof(f1509,plain,
    ( ~ sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)
    | spl9_54 ),
    inference(resolution,[],[f1487,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1487,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))
    | spl9_54 ),
    inference(avatar_component_clause,[],[f1485])).

fof(f1345,plain,
    ( ~ spl9_47
    | ~ spl9_49 ),
    inference(avatar_contradiction_clause,[],[f1344])).

fof(f1344,plain,
    ( $false
    | ~ spl9_47
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f1338,f108])).

fof(f108,plain,(
    ! [X1] : ~ sP1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1338,plain,
    ( sP1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_47
    | ~ spl9_49 ),
    inference(backward_demodulation,[],[f1177,f1208])).

fof(f1208,plain,
    ( k1_xboole_0 = u1_struct_0(sK6)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f1206])).

fof(f1177,plain,
    ( sP1(u1_struct_0(sK6),k1_xboole_0)
    | ~ spl9_47 ),
    inference(backward_demodulation,[],[f1114,f1160])).

fof(f1209,plain,
    ( spl9_48
    | spl9_49
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f1200,f1112,f1206,f1202])).

fof(f1200,plain,
    ( k1_xboole_0 = u1_struct_0(sK6)
    | k1_xboole_0 = sK8
    | ~ spl9_47 ),
    inference(subsumption_resolution,[],[f1198,f1169])).

fof(f1169,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),k1_xboole_0)
    | ~ spl9_47 ),
    inference(backward_demodulation,[],[f209,f1160])).

fof(f1198,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK6)
    | k1_xboole_0 = sK8
    | ~ spl9_47 ),
    inference(resolution,[],[f1172,f107])).

fof(f1172,plain,
    ( sP3(sK8,k1_xboole_0,u1_struct_0(sK6))
    | ~ spl9_47 ),
    inference(backward_demodulation,[],[f216,f1160])).

fof(f216,plain,(
    sP3(sK8,k2_relat_1(sK8),u1_struct_0(sK6)) ),
    inference(backward_demodulation,[],[f161,f196])).

fof(f161,plain,(
    sP3(sK8,k2_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f93,f125])).

fof(f1149,plain,
    ( spl9_47
    | ~ spl9_30
    | spl9_31 ),
    inference(avatar_split_clause,[],[f970,f642,f638,f1112])).

fof(f638,plain,
    ( spl9_30
  <=> m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f642,plain,
    ( spl9_31
  <=> u1_struct_0(sK6) = k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f970,plain,
    ( sP1(u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f969,f732])).

fof(f732,plain,
    ( u1_struct_0(sK6) != k1_relat_1(sK8)
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f731,f143])).

fof(f143,plain,(
    v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f139,f83])).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,
    ( v1_relat_1(sK8)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))) ),
    inference(resolution,[],[f75,f69])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f731,plain,
    ( u1_struct_0(sK6) != k1_relat_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f730,f67])).

fof(f730,plain,
    ( u1_struct_0(sK6) != k1_relat_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f729,f71])).

fof(f71,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f729,plain,
    ( u1_struct_0(sK6) != k1_relat_1(sK8)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_30
    | spl9_31 ),
    inference(superposition,[],[f724,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f724,plain,
    ( u1_struct_0(sK6) != k2_relat_1(k2_funct_1(sK8))
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f721,f639])).

fof(f639,plain,
    ( m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f638])).

fof(f721,plain,
    ( u1_struct_0(sK6) != k2_relat_1(k2_funct_1(sK8))
    | ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))
    | spl9_31 ),
    inference(superposition,[],[f644,f85])).

fof(f644,plain,
    ( u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f642])).

fof(f969,plain,
    ( sP1(u1_struct_0(sK6),k2_relat_1(sK8))
    | u1_struct_0(sK6) = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f936,f209])).

fof(f936,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | sP1(u1_struct_0(sK6),k2_relat_1(sK8))
    | u1_struct_0(sK6) = k1_relat_1(sK8) ),
    inference(resolution,[],[f273,f208])).

fof(f273,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f271,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f271,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f88,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f822,plain,(
    spl9_33 ),
    inference(avatar_contradiction_clause,[],[f821])).

fof(f821,plain,
    ( $false
    | spl9_33 ),
    inference(subsumption_resolution,[],[f820,f143])).

fof(f820,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_33 ),
    inference(subsumption_resolution,[],[f819,f67])).

fof(f819,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_33 ),
    inference(subsumption_resolution,[],[f818,f71])).

fof(f818,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_33 ),
    inference(subsumption_resolution,[],[f816,f297])).

fof(f816,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_33 ),
    inference(superposition,[],[f652,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f652,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8)
    | spl9_33 ),
    inference(avatar_component_clause,[],[f650])).

fof(f650,plain,
    ( spl9_33
  <=> r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f719,plain,(
    spl9_32 ),
    inference(avatar_contradiction_clause,[],[f718])).

fof(f718,plain,
    ( $false
    | spl9_32 ),
    inference(subsumption_resolution,[],[f717,f143])).

fof(f717,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_32 ),
    inference(subsumption_resolution,[],[f716,f67])).

fof(f716,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_32 ),
    inference(subsumption_resolution,[],[f715,f71])).

fof(f715,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_32 ),
    inference(resolution,[],[f714,f79])).

fof(f79,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f24,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f714,plain,
    ( ~ sP0(sK8)
    | spl9_32 ),
    inference(resolution,[],[f648,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f648,plain,
    ( ~ v2_funct_1(k2_funct_1(sK8))
    | spl9_32 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl9_32
  <=> v2_funct_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f657,plain,
    ( ~ spl9_1
    | spl9_30 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | ~ spl9_1
    | spl9_30 ),
    inference(subsumption_resolution,[],[f654,f328])).

fof(f328,plain,
    ( sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl9_1
  <=> sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f654,plain,
    ( ~ sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | spl9_30 ),
    inference(resolution,[],[f640,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP5(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f640,plain,
    ( ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))
    | spl9_30 ),
    inference(avatar_component_clause,[],[f638])).

fof(f653,plain,
    ( ~ spl9_30
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_33
    | ~ spl9_1
    | spl9_16
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f636,f491,f446,f326,f650,f646,f642,f638])).

fof(f446,plain,
    ( spl9_16
  <=> r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f491,plain,
    ( spl9_25
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8),k2_relat_1(sK8),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f636,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8)
    | ~ v2_funct_1(k2_funct_1(sK8))
    | u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8))
    | ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))
    | ~ spl9_1
    | spl9_16
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f635,f359])).

fof(f359,plain,
    ( v1_funct_1(k2_funct_1(sK8))
    | ~ spl9_1 ),
    inference(resolution,[],[f328,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f635,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8)
    | ~ v2_funct_1(k2_funct_1(sK8))
    | u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8))
    | ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | spl9_16
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f632,f608])).

fof(f608,plain,
    ( v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f607,f67])).

fof(f607,plain,
    ( v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f606,f209])).

fof(f606,plain,
    ( v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f605,f208])).

fof(f605,plain,
    ( v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f604,f207])).

fof(f207,plain,(
    k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8) ),
    inference(backward_demodulation,[],[f124,f196])).

fof(f124,plain,(
    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),k2_struct_0(sK7),sK8) ),
    inference(subsumption_resolution,[],[f116,f66])).

fof(f116,plain,
    ( k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),k2_struct_0(sK7),sK8)
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f70,f73])).

fof(f604,plain,
    ( v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f602,f71])).

fof(f602,plain,
    ( v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ v2_funct_1(sK8)
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ spl9_25 ),
    inference(superposition,[],[f492,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f492,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f491])).

fof(f632,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8)
    | ~ v2_funct_1(k2_funct_1(sK8))
    | u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8))
    | ~ m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))
    | ~ v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | spl9_16 ),
    inference(superposition,[],[f448,f102])).

fof(f448,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f446])).

fof(f629,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f383,f446])).

fof(f383,plain,(
    ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) ),
    inference(subsumption_resolution,[],[f382,f67])).

fof(f382,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f381,f209])).

fof(f381,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f380,f208])).

fof(f380,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f379,f207])).

fof(f379,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f368,f71])).

fof(f368,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)
    | ~ v2_funct_1(sK8)
    | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(superposition,[],[f206,f102])).

fof(f569,plain,(
    spl9_25 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | spl9_25 ),
    inference(subsumption_resolution,[],[f565,f254])).

fof(f565,plain,
    ( ~ sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | spl9_25 ),
    inference(resolution,[],[f493,f95])).

fof(f493,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8),k2_relat_1(sK8),u1_struct_0(sK6))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f491])).

fof(f348,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f347,f326])).

fof(f347,plain,(
    sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) ),
    inference(subsumption_resolution,[],[f346,f67])).

fof(f346,plain,
    ( sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f345,f209])).

fof(f345,plain,
    ( sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f344,f71])).

fof(f344,plain,
    ( ~ v2_funct_1(sK8)
    | sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(subsumption_resolution,[],[f316,f207])).

fof(f316,plain,
    ( k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v2_funct_1(sK8)
    | sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[],[f101,f208])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP5(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f36,f49])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (15101)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.46  % (15119)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.47  % (15111)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (15103)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (15120)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (15097)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (15112)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (15104)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (15116)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (15115)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (15100)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (15108)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (15105)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (15098)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (15099)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (15102)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (15113)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (15109)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (15110)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (15117)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (15122)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (15101)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2360,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f348,f569,f629,f653,f657,f719,f822,f1149,f1209,f1345,f1513,f1716,f1818,f2359])).
% 0.22/0.54  fof(f2359,plain,(
% 0.22/0.54    ~spl9_47 | ~spl9_48 | spl9_49 | ~spl9_54 | ~spl9_55 | ~spl9_56),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f2358])).
% 0.22/0.54  fof(f2358,plain,(
% 0.22/0.54    $false | (~spl9_47 | ~spl9_48 | spl9_49 | ~spl9_54 | ~spl9_55 | ~spl9_56)),
% 0.22/0.54    inference(subsumption_resolution,[],[f2357,f1848])).
% 0.22/0.54  fof(f1848,plain,(
% 0.22/0.54    sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | (~spl9_54 | ~spl9_55 | ~spl9_56)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1847,f1486])).
% 0.22/0.54  fof(f1486,plain,(
% 0.22/0.54    v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | ~spl9_54),
% 0.22/0.54    inference(avatar_component_clause,[],[f1485])).
% 0.22/0.54  fof(f1485,plain,(
% 0.22/0.54    spl9_54 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 0.22/0.54  fof(f1847,plain,(
% 0.22/0.54    sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | (~spl9_55 | ~spl9_56)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1836,f1490])).
% 0.22/0.54  fof(f1490,plain,(
% 0.22/0.54    v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6)) | ~spl9_55),
% 0.22/0.54    inference(avatar_component_clause,[],[f1489])).
% 0.22/0.54  fof(f1489,plain,(
% 0.22/0.54    spl9_55 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 0.22/0.54  fof(f1836,plain,(
% 0.22/0.54    sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | ~spl9_56),
% 0.22/0.54    inference(resolution,[],[f1494,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (sP4(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(definition_folding,[],[f34,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP4(X0,X1,X2))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.54  fof(f1494,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) | ~spl9_56),
% 0.22/0.54    inference(avatar_component_clause,[],[f1493])).
% 0.22/0.54  fof(f1493,plain,(
% 0.22/0.54    spl9_56 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 0.22/0.54  fof(f2357,plain,(
% 0.22/0.54    ~sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | (~spl9_47 | ~spl9_48 | spl9_49)),
% 0.22/0.54    inference(subsumption_resolution,[],[f2356,f1207])).
% 0.22/0.54  fof(f1207,plain,(
% 0.22/0.54    k1_xboole_0 != u1_struct_0(sK6) | spl9_49),
% 0.22/0.54    inference(avatar_component_clause,[],[f1206])).
% 0.22/0.54  fof(f1206,plain,(
% 0.22/0.54    spl9_49 <=> k1_xboole_0 = u1_struct_0(sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.22/0.54  fof(f2356,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(sK6) | ~sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | (~spl9_47 | ~spl9_48)),
% 0.22/0.54    inference(subsumption_resolution,[],[f2328,f1389])).
% 0.22/0.54  fof(f1389,plain,(
% 0.22/0.54    r2_funct_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl9_47 | ~spl9_48)),
% 0.22/0.54    inference(forward_demodulation,[],[f1388,f1218])).
% 0.22/0.54  fof(f1218,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl9_47 | ~spl9_48)),
% 0.22/0.54    inference(backward_demodulation,[],[f1160,f1204])).
% 0.22/0.54  fof(f1204,plain,(
% 0.22/0.54    k1_xboole_0 = sK8 | ~spl9_48),
% 0.22/0.54    inference(avatar_component_clause,[],[f1202])).
% 0.22/0.54  fof(f1202,plain,(
% 0.22/0.54    spl9_48 <=> k1_xboole_0 = sK8),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 0.22/0.54  fof(f1160,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(sK8) | ~spl9_47),
% 0.22/0.54    inference(resolution,[],[f1114,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f1114,plain,(
% 0.22/0.54    sP1(u1_struct_0(sK6),k2_relat_1(sK8)) | ~spl9_47),
% 0.22/0.54    inference(avatar_component_clause,[],[f1112])).
% 0.22/0.54  fof(f1112,plain,(
% 0.22/0.54    spl9_47 <=> sP1(u1_struct_0(sK6),k2_relat_1(sK8))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 0.22/0.54  fof(f1388,plain,(
% 0.22/0.54    r2_funct_2(u1_struct_0(sK6),k2_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~spl9_48),
% 0.22/0.54    inference(forward_demodulation,[],[f297,f1204])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f296,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    v1_funct_1(sK8)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ((~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),sK8) & v2_funct_1(sK8) & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_struct_0(sK7) & ~v2_struct_0(sK7)) & l1_struct_0(sK6)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f18,f53,f52,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK6))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X2) = k2_struct_0(sK7) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_struct_0(sK7) & ~v2_struct_0(sK7))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ? [X2] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),X2) = k2_struct_0(sK7) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),sK8) & v2_funct_1(sK8) & k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f15])).
% 0.22/0.54  fof(f15,conjecture,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f288,f209])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8))),
% 0.22/0.54    inference(backward_demodulation,[],[f126,f196])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    k2_struct_0(sK7) = k2_relat_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f188,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    k2_struct_0(sK7) = k2_relat_1(sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 0.22/0.54    inference(superposition,[],[f85,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    v1_funct_2(sK8,u1_struct_0(sK6),k2_struct_0(sK7))),
% 0.22/0.54    inference(subsumption_resolution,[],[f118,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    l1_struct_0(sK7)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    v1_funct_2(sK8,u1_struct_0(sK6),k2_struct_0(sK7)) | ~l1_struct_0(sK7)),
% 0.22/0.54    inference(superposition,[],[f68,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f288,plain,(
% 0.22/0.54    r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(resolution,[],[f110,f208])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8))))),
% 0.22/0.54    inference(backward_demodulation,[],[f125,f196])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK7))))),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f66])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK7)))) | ~l1_struct_0(sK7)),
% 0.22/0.54    inference(superposition,[],[f69,f73])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(equality_resolution,[],[f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.54  fof(f2328,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK6) | ~sP4(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | (~spl9_47 | ~spl9_48)),
% 0.22/0.54    inference(superposition,[],[f1471,f727])).
% 0.22/0.54  fof(f727,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_tops_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | ~sP4(k1_xboole_0,X0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f725,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP4(X0,X1,X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f47])).
% 0.22/0.54  fof(f725,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP4(k1_xboole_0,X0,X1) | ~v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = k2_tops_2(k1_xboole_0,X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f223,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~sP3(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(equality_resolution,[],[f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2))),
% 0.22/0.54    inference(rectify,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP3(k2_tops_2(X0,X1,X2),X0,X1) | ~sP4(X0,X1,X2)) )),
% 0.22/0.54    inference(resolution,[],[f96,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X2,X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(definition_folding,[],[f32,f45,f44,f43])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f61])).
% 0.22/0.54  fof(f1471,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k1_xboole_0,k2_tops_2(k1_xboole_0,u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl9_47 | ~spl9_48)),
% 0.22/0.54    inference(forward_demodulation,[],[f1470,f1218])).
% 0.22/0.54  fof(f1470,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) | ~spl9_48),
% 0.22/0.54    inference(forward_demodulation,[],[f206,f1204])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8)),sK8)),
% 0.22/0.54    inference(backward_demodulation,[],[f123,f196])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_struct_0(sK7),k2_tops_2(k2_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_struct_0(sK7),sK8)),sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f115,f66])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_struct_0(sK7),k2_tops_2(k2_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),k2_struct_0(sK7),sK8)),sK8) | ~l1_struct_0(sK7)),
% 0.22/0.54    inference(superposition,[],[f72,f73])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK7),k2_tops_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tops_2(u1_struct_0(sK6),u1_struct_0(sK7),sK8)),sK8)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f1818,plain,(
% 0.22/0.54    ~spl9_47 | ~spl9_48 | spl9_56),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1817])).
% 0.22/0.54  fof(f1817,plain,(
% 0.22/0.54    $false | (~spl9_47 | ~spl9_48 | spl9_56)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1813,f1224])).
% 0.22/0.54  fof(f1224,plain,(
% 0.22/0.54    sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0) | (~spl9_47 | ~spl9_48)),
% 0.22/0.54    inference(forward_demodulation,[],[f1173,f1204])).
% 0.22/0.54  fof(f1173,plain,(
% 0.22/0.54    sP4(u1_struct_0(sK6),k1_xboole_0,sK8) | ~spl9_47),
% 0.22/0.54    inference(backward_demodulation,[],[f254,f1160])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f253,f67])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f245,f209])).
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(resolution,[],[f97,f208])).
% 0.22/0.54  fof(f1813,plain,(
% 0.22/0.54    ~sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0) | spl9_56),
% 0.22/0.54    inference(resolution,[],[f1495,f96])).
% 0.22/0.54  fof(f1495,plain,(
% 0.22/0.54    ~m1_subset_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) | spl9_56),
% 0.22/0.54    inference(avatar_component_clause,[],[f1493])).
% 0.22/0.54  fof(f1716,plain,(
% 0.22/0.54    ~spl9_47 | ~spl9_48 | spl9_55),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1715])).
% 0.22/0.54  fof(f1715,plain,(
% 0.22/0.54    $false | (~spl9_47 | ~spl9_48 | spl9_55)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1712,f1224])).
% 0.22/0.54  fof(f1712,plain,(
% 0.22/0.54    ~sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0) | spl9_55),
% 0.22/0.54    inference(resolution,[],[f1491,f95])).
% 0.22/0.54  fof(f1491,plain,(
% 0.22/0.54    ~v1_funct_2(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0),k1_xboole_0,u1_struct_0(sK6)) | spl9_55),
% 0.22/0.54    inference(avatar_component_clause,[],[f1489])).
% 0.22/0.54  fof(f1513,plain,(
% 0.22/0.54    ~spl9_47 | ~spl9_48 | spl9_54),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1512])).
% 0.22/0.54  fof(f1512,plain,(
% 0.22/0.54    $false | (~spl9_47 | ~spl9_48 | spl9_54)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1509,f1224])).
% 0.22/0.54  fof(f1509,plain,(
% 0.22/0.54    ~sP4(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0) | spl9_54),
% 0.22/0.54    inference(resolution,[],[f1487,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~sP4(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f61])).
% 0.22/0.54  fof(f1487,plain,(
% 0.22/0.54    ~v1_funct_1(k2_tops_2(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0)) | spl9_54),
% 0.22/0.54    inference(avatar_component_clause,[],[f1485])).
% 0.22/0.54  fof(f1345,plain,(
% 0.22/0.54    ~spl9_47 | ~spl9_49),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1344])).
% 0.22/0.54  fof(f1344,plain,(
% 0.22/0.54    $false | (~spl9_47 | ~spl9_49)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1338,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X1] : (~sP1(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f60])).
% 0.22/0.54  fof(f1338,plain,(
% 0.22/0.54    sP1(k1_xboole_0,k1_xboole_0) | (~spl9_47 | ~spl9_49)),
% 0.22/0.54    inference(backward_demodulation,[],[f1177,f1208])).
% 0.22/0.54  fof(f1208,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(sK6) | ~spl9_49),
% 0.22/0.54    inference(avatar_component_clause,[],[f1206])).
% 0.22/0.54  fof(f1177,plain,(
% 0.22/0.54    sP1(u1_struct_0(sK6),k1_xboole_0) | ~spl9_47),
% 0.22/0.54    inference(backward_demodulation,[],[f1114,f1160])).
% 0.22/0.54  fof(f1209,plain,(
% 0.22/0.54    spl9_48 | spl9_49 | ~spl9_47),
% 0.22/0.54    inference(avatar_split_clause,[],[f1200,f1112,f1206,f1202])).
% 0.22/0.54  fof(f1200,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(sK6) | k1_xboole_0 = sK8 | ~spl9_47),
% 0.22/0.54    inference(subsumption_resolution,[],[f1198,f1169])).
% 0.22/0.54  fof(f1169,plain,(
% 0.22/0.54    v1_funct_2(sK8,u1_struct_0(sK6),k1_xboole_0) | ~spl9_47),
% 0.22/0.54    inference(backward_demodulation,[],[f209,f1160])).
% 0.22/0.54  fof(f1198,plain,(
% 0.22/0.54    ~v1_funct_2(sK8,u1_struct_0(sK6),k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK6) | k1_xboole_0 = sK8 | ~spl9_47),
% 0.22/0.54    inference(resolution,[],[f1172,f107])).
% 0.22/0.54  fof(f1172,plain,(
% 0.22/0.54    sP3(sK8,k1_xboole_0,u1_struct_0(sK6)) | ~spl9_47),
% 0.22/0.54    inference(backward_demodulation,[],[f216,f1160])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    sP3(sK8,k2_relat_1(sK8),u1_struct_0(sK6))),
% 0.22/0.54    inference(backward_demodulation,[],[f161,f196])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    sP3(sK8,k2_struct_0(sK7),u1_struct_0(sK6))),
% 0.22/0.54    inference(resolution,[],[f93,f125])).
% 0.22/0.54  fof(f1149,plain,(
% 0.22/0.54    spl9_47 | ~spl9_30 | spl9_31),
% 0.22/0.54    inference(avatar_split_clause,[],[f970,f642,f638,f1112])).
% 0.22/0.54  fof(f638,plain,(
% 0.22/0.54    spl9_30 <=> m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.22/0.54  fof(f642,plain,(
% 0.22/0.54    spl9_31 <=> u1_struct_0(sK6) = k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.54  fof(f970,plain,(
% 0.22/0.54    sP1(u1_struct_0(sK6),k2_relat_1(sK8)) | (~spl9_30 | spl9_31)),
% 0.22/0.54    inference(subsumption_resolution,[],[f969,f732])).
% 0.22/0.54  fof(f732,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k1_relat_1(sK8) | (~spl9_30 | spl9_31)),
% 0.22/0.54    inference(subsumption_resolution,[],[f731,f143])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    v1_relat_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f139,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    v1_relat_1(sK8) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))),
% 0.22/0.54    inference(resolution,[],[f75,f69])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.54  fof(f731,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k1_relat_1(sK8) | ~v1_relat_1(sK8) | (~spl9_30 | spl9_31)),
% 0.22/0.54    inference(subsumption_resolution,[],[f730,f67])).
% 0.22/0.54  fof(f730,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k1_relat_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_30 | spl9_31)),
% 0.22/0.54    inference(subsumption_resolution,[],[f729,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    v2_funct_1(sK8)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f729,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k1_relat_1(sK8) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_30 | spl9_31)),
% 0.22/0.54    inference(superposition,[],[f724,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.54  fof(f724,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k2_relat_1(k2_funct_1(sK8)) | (~spl9_30 | spl9_31)),
% 0.22/0.54    inference(subsumption_resolution,[],[f721,f639])).
% 0.22/0.54  fof(f639,plain,(
% 0.22/0.54    m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) | ~spl9_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f638])).
% 0.22/0.54  fof(f721,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k2_relat_1(k2_funct_1(sK8)) | ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) | spl9_31),
% 0.22/0.54    inference(superposition,[],[f644,f85])).
% 0.22/0.54  fof(f644,plain,(
% 0.22/0.54    u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)) | spl9_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f642])).
% 0.22/0.54  fof(f969,plain,(
% 0.22/0.54    sP1(u1_struct_0(sK6),k2_relat_1(sK8)) | u1_struct_0(sK6) = k1_relat_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f936,f209])).
% 0.22/0.54  fof(f936,plain,(
% 0.22/0.54    ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | sP1(u1_struct_0(sK6),k2_relat_1(sK8)) | u1_struct_0(sK6) = k1_relat_1(sK8)),
% 0.22/0.54    inference(resolution,[],[f273,f208])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f271,f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.54    inference(superposition,[],[f88,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.22/0.54    inference(rectify,[],[f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f44])).
% 0.22/0.54  fof(f822,plain,(
% 0.22/0.54    spl9_33),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f821])).
% 0.22/0.54  fof(f821,plain,(
% 0.22/0.54    $false | spl9_33),
% 0.22/0.54    inference(subsumption_resolution,[],[f820,f143])).
% 0.22/0.54  fof(f820,plain,(
% 0.22/0.54    ~v1_relat_1(sK8) | spl9_33),
% 0.22/0.54    inference(subsumption_resolution,[],[f819,f67])).
% 0.22/0.54  fof(f819,plain,(
% 0.22/0.54    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_33),
% 0.22/0.54    inference(subsumption_resolution,[],[f818,f71])).
% 0.22/0.54  fof(f818,plain,(
% 0.22/0.54    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_33),
% 0.22/0.54    inference(subsumption_resolution,[],[f816,f297])).
% 0.22/0.54  fof(f816,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8,sK8) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_33),
% 0.22/0.54    inference(superposition,[],[f652,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.54  fof(f652,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8) | spl9_33),
% 0.22/0.54    inference(avatar_component_clause,[],[f650])).
% 0.22/0.54  fof(f650,plain,(
% 0.22/0.54    spl9_33 <=> r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.22/0.54  fof(f719,plain,(
% 0.22/0.54    spl9_32),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f718])).
% 0.22/0.54  fof(f718,plain,(
% 0.22/0.54    $false | spl9_32),
% 0.22/0.54    inference(subsumption_resolution,[],[f717,f143])).
% 0.22/0.54  fof(f717,plain,(
% 0.22/0.54    ~v1_relat_1(sK8) | spl9_32),
% 0.22/0.54    inference(subsumption_resolution,[],[f716,f67])).
% 0.22/0.54  fof(f716,plain,(
% 0.22/0.54    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_32),
% 0.22/0.54    inference(subsumption_resolution,[],[f715,f71])).
% 0.22/0.54  fof(f715,plain,(
% 0.22/0.54    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_32),
% 0.22/0.54    inference(resolution,[],[f714,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(definition_folding,[],[f24,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.54  fof(f714,plain,(
% 0.22/0.54    ~sP0(sK8) | spl9_32),
% 0.22/0.54    inference(resolution,[],[f648,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f41])).
% 0.22/0.54  fof(f648,plain,(
% 0.22/0.54    ~v2_funct_1(k2_funct_1(sK8)) | spl9_32),
% 0.22/0.54    inference(avatar_component_clause,[],[f646])).
% 0.22/0.54  fof(f646,plain,(
% 0.22/0.54    spl9_32 <=> v2_funct_1(k2_funct_1(sK8))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.54  fof(f657,plain,(
% 0.22/0.54    ~spl9_1 | spl9_30),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f656])).
% 0.22/0.54  fof(f656,plain,(
% 0.22/0.54    $false | (~spl9_1 | spl9_30)),
% 0.22/0.54    inference(subsumption_resolution,[],[f654,f328])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~spl9_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f326])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    spl9_1 <=> sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.54  fof(f654,plain,(
% 0.22/0.54    ~sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | spl9_30),
% 0.22/0.54    inference(resolution,[],[f640,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP5(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP5(X0,X1,X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP5(X0,X1,X2))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.54  fof(f640,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) | spl9_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f638])).
% 0.22/0.54  fof(f653,plain,(
% 0.22/0.54    ~spl9_30 | ~spl9_31 | ~spl9_32 | ~spl9_33 | ~spl9_1 | spl9_16 | ~spl9_25),
% 0.22/0.54    inference(avatar_split_clause,[],[f636,f491,f446,f326,f650,f646,f642,f638])).
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    spl9_16 <=> r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.54  fof(f491,plain,(
% 0.22/0.54    spl9_25 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8),k2_relat_1(sK8),u1_struct_0(sK6))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.54  fof(f636,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8) | ~v2_funct_1(k2_funct_1(sK8)) | u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)) | ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) | (~spl9_1 | spl9_16 | ~spl9_25)),
% 0.22/0.54    inference(subsumption_resolution,[],[f635,f359])).
% 0.22/0.54  fof(f359,plain,(
% 0.22/0.54    v1_funct_1(k2_funct_1(sK8)) | ~spl9_1),
% 0.22/0.54    inference(resolution,[],[f328,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | v1_funct_1(k2_funct_1(X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f62])).
% 0.22/0.54  fof(f635,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8) | ~v2_funct_1(k2_funct_1(sK8)) | u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)) | ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) | ~v1_funct_1(k2_funct_1(sK8)) | (spl9_16 | ~spl9_25)),
% 0.22/0.54    inference(subsumption_resolution,[],[f632,f608])).
% 0.22/0.54  fof(f608,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~spl9_25),
% 0.22/0.54    inference(subsumption_resolution,[],[f607,f67])).
% 0.22/0.54  fof(f607,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK8) | ~spl9_25),
% 0.22/0.54    inference(subsumption_resolution,[],[f606,f209])).
% 0.22/0.54  fof(f606,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | ~spl9_25),
% 0.22/0.54    inference(subsumption_resolution,[],[f605,f208])).
% 0.22/0.54  fof(f605,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | ~spl9_25),
% 0.22/0.54    inference(subsumption_resolution,[],[f604,f207])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    k2_relat_1(sK8) = k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8)),
% 0.22/0.54    inference(backward_demodulation,[],[f124,f196])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),k2_struct_0(sK7),sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f116,f66])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    k2_struct_0(sK7) = k2_relset_1(u1_struct_0(sK6),k2_struct_0(sK7),sK8) | ~l1_struct_0(sK7)),
% 0.22/0.54    inference(superposition,[],[f70,f73])).
% 0.22/0.54  fof(f604,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | ~spl9_25),
% 0.22/0.54    inference(subsumption_resolution,[],[f602,f71])).
% 0.22/0.54  fof(f602,plain,(
% 0.22/0.54    v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~v2_funct_1(sK8) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8) | ~spl9_25),
% 0.22/0.54    inference(superposition,[],[f492,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.54  fof(f492,plain,(
% 0.22/0.54    v1_funct_2(k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~spl9_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f491])).
% 0.22/0.54  fof(f632,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_funct_1(k2_funct_1(sK8)),sK8) | ~v2_funct_1(k2_funct_1(sK8)) | u1_struct_0(sK6) != k2_relset_1(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)) | ~m1_subset_1(k2_funct_1(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(k2_funct_1(sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | ~v1_funct_1(k2_funct_1(sK8)) | spl9_16),
% 0.22/0.54    inference(superposition,[],[f448,f102])).
% 0.22/0.54  fof(f448,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) | spl9_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f446])).
% 0.22/0.54  fof(f629,plain,(
% 0.22/0.54    ~spl9_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f383,f446])).
% 0.22/0.54  fof(f383,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f382,f67])).
% 0.22/0.54  fof(f382,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f381,f209])).
% 0.22/0.54  fof(f381,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f380,f208])).
% 0.22/0.54  fof(f380,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f379,f207])).
% 0.22/0.54  fof(f379,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f368,f71])).
% 0.22/0.54  fof(f368,plain,(
% 0.22/0.54    ~r2_funct_2(u1_struct_0(sK6),k2_relat_1(sK8),k2_tops_2(k2_relat_1(sK8),u1_struct_0(sK6),k2_funct_1(sK8)),sK8) | ~v2_funct_1(sK8) | k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_relat_1(sK8)))) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(superposition,[],[f206,f102])).
% 0.22/0.54  fof(f569,plain,(
% 0.22/0.54    spl9_25),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f568])).
% 0.22/0.54  fof(f568,plain,(
% 0.22/0.54    $false | spl9_25),
% 0.22/0.54    inference(subsumption_resolution,[],[f565,f254])).
% 0.22/0.54  fof(f565,plain,(
% 0.22/0.54    ~sP4(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | spl9_25),
% 0.22/0.54    inference(resolution,[],[f493,f95])).
% 0.22/0.54  fof(f493,plain,(
% 0.22/0.54    ~v1_funct_2(k2_tops_2(u1_struct_0(sK6),k2_relat_1(sK8),sK8),k2_relat_1(sK8),u1_struct_0(sK6)) | spl9_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f491])).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    spl9_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f347,f326])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f346,f67])).
% 0.22/0.54  fof(f346,plain,(
% 0.22/0.54    sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f345,f209])).
% 0.22/0.54  fof(f345,plain,(
% 0.22/0.54    sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f344,f71])).
% 0.22/0.54  fof(f344,plain,(
% 0.22/0.54    ~v2_funct_1(sK8) | sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f316,f207])).
% 0.22/0.54  fof(f316,plain,(
% 0.22/0.54    k2_relat_1(sK8) != k2_relset_1(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v2_funct_1(sK8) | sP5(u1_struct_0(sK6),k2_relat_1(sK8),sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),k2_relat_1(sK8)) | ~v1_funct_1(sK8)),
% 0.22/0.54    inference(resolution,[],[f101,f208])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP5(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (sP5(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(definition_folding,[],[f36,f49])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (15101)------------------------------
% 0.22/0.55  % (15101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15101)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (15101)Memory used [KB]: 7164
% 0.22/0.55  % (15101)Time elapsed: 0.148 s
% 0.22/0.55  % (15101)------------------------------
% 0.22/0.55  % (15101)------------------------------
% 0.22/0.55  % (15096)Success in time 0.184 s
%------------------------------------------------------------------------------
