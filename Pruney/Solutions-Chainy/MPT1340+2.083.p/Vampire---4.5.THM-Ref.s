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
% DateTime   : Thu Dec  3 13:14:30 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  339 (4129 expanded)
%              Number of leaves         :   45 (1386 expanded)
%              Depth                    :   32
%              Number of atoms          : 1422 (27559 expanded)
%              Number of equality atoms :  209 (4226 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f150,f162,f168,f174,f215,f315,f375,f493,f608,f714,f1337,f1370,f1451,f1515,f1612,f1667,f1675,f1683,f1779,f1782,f2274,f2341,f2354,f2361])).

fof(f2361,plain,
    ( ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62
    | ~ spl3_65
    | ~ spl3_75 ),
    inference(avatar_contradiction_clause,[],[f2360])).

fof(f2360,plain,
    ( $false
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62
    | ~ spl3_65
    | ~ spl3_75 ),
    inference(subsumption_resolution,[],[f2358,f1815])).

fof(f1815,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1814,f494])).

fof(f494,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f69,f370])).

fof(f370,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl3_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f1814,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1805,f1641])).

fof(f1641,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(backward_demodulation,[],[f1560,f1598])).

fof(f1598,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f1596])).

fof(f1596,plain,
    ( spl3_62
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1560,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0))
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f963,f370])).

fof(f963,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f176,f470])).

fof(f470,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f176,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f175,f129])).

fof(f129,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f175,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f70,f128])).

fof(f128,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f67,f78])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f1805,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(resolution,[],[f1793,f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1793,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f1578,f1598])).

fof(f1578,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0))))
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f962,f370])).

fof(f962,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f178,f470])).

fof(f178,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f177,f128])).

fof(f177,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f71,f129])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f2358,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62
    | ~ spl3_65
    | ~ spl3_75 ),
    inference(backward_demodulation,[],[f1934,f2080])).

fof(f2080,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f2078])).

fof(f2078,plain,
    ( spl3_75
  <=> k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f1934,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62
    | ~ spl3_65 ),
    inference(backward_demodulation,[],[f1858,f1666])).

fof(f1666,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f1664])).

fof(f1664,plain,
    ( spl3_65
  <=> k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1858,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f1780,f1598])).

fof(f1780,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1706,f128])).

fof(f1706,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f965,f370])).

fof(f965,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f448,f470])).

fof(f448,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f74,f129])).

fof(f74,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f2354,plain,
    ( ~ spl3_19
    | ~ spl3_66
    | ~ spl3_67
    | spl3_78 ),
    inference(avatar_contradiction_clause,[],[f2353])).

fof(f2353,plain,
    ( $false
    | ~ spl3_19
    | ~ spl3_66
    | ~ spl3_67
    | spl3_78 ),
    inference(subsumption_resolution,[],[f2352,f504])).

fof(f504,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f234,f370])).

fof(f234,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f233,f69])).

fof(f233,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f232,f176])).

fof(f232,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f231,f178])).

fof(f231,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f225,f73])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f225,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f109,f218])).

fof(f218,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f217,f128])).

fof(f217,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f72,f129])).

fof(f72,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f2352,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_66
    | ~ spl3_67
    | spl3_78 ),
    inference(subsumption_resolution,[],[f2351,f1674])).

fof(f1674,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1672])).

fof(f1672,plain,
    ( spl3_66
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f2351,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_67
    | spl3_78 ),
    inference(subsumption_resolution,[],[f2350,f1682])).

fof(f1682,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f1680])).

fof(f1680,plain,
    ( spl3_67
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f2350,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | spl3_78 ),
    inference(resolution,[],[f2273,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f2273,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | spl3_78 ),
    inference(avatar_component_clause,[],[f2271])).

fof(f2271,plain,
    ( spl3_78
  <=> v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f2341,plain,
    ( spl3_15
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(avatar_contradiction_clause,[],[f2340])).

fof(f2340,plain,
    ( $false
    | spl3_15
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f2339,f1793])).

fof(f2339,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_15
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f302,f370])).

fof(f302,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f2274,plain,
    ( spl3_75
    | ~ spl3_78
    | ~ spl3_17
    | ~ spl3_19
    | spl3_20
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f2269,f1680,f372,f368,f312,f2271,f2078])).

fof(f312,plain,
    ( spl3_17
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f372,plain,
    ( spl3_20
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2269,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_17
    | ~ spl3_19
    | spl3_20
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f2259,f373])).

fof(f373,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f372])).

fof(f2259,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_67 ),
    inference(resolution,[],[f1963,f120])).

fof(f120,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1963,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f1962,f504])).

fof(f1962,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_67 ),
    inference(subsumption_resolution,[],[f1951,f1717])).

fof(f1717,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f314,f370])).

fof(f314,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f312])).

fof(f1951,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_67 ),
    inference(resolution,[],[f1682,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1782,plain,
    ( spl3_10
    | ~ spl3_19
    | ~ spl3_63 ),
    inference(avatar_contradiction_clause,[],[f1781])).

fof(f1781,plain,
    ( $false
    | spl3_10
    | ~ spl3_19
    | ~ spl3_63 ),
    inference(subsumption_resolution,[],[f1611,f1580])).

fof(f1580,plain,
    ( ~ v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f208,f370])).

fof(f208,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl3_10
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1611,plain,
    ( v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f1609])).

fof(f1609,plain,
    ( spl3_63
  <=> v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f1779,plain,
    ( ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62
    | spl3_64 ),
    inference(avatar_contradiction_clause,[],[f1778])).

fof(f1778,plain,
    ( $false
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62
    | spl3_64 ),
    inference(subsumption_resolution,[],[f1662,f1640])).

fof(f1640,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(backward_demodulation,[],[f1578,f1598])).

fof(f1662,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_64 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f1660,plain,
    ( spl3_64
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1683,plain,
    ( ~ spl3_64
    | spl3_67
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f1678,f1596,f469,f368,f1680,f1660])).

fof(f1678,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1677,f494])).

fof(f1677,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1676,f1641])).

fof(f1676,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1652,f495])).

fof(f495,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f73,f370])).

fof(f1652,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(trivial_inequality_removal,[],[f1651])).

fof(f1651,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(superposition,[],[f111,f1639])).

fof(f1639,plain,
    ( k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(backward_demodulation,[],[f1617,f1598])).

fof(f1617,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f964,f370])).

fof(f964,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f218,f470])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1675,plain,
    ( ~ spl3_64
    | spl3_66
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f1670,f1596,f469,f368,f1672,f1660])).

fof(f1670,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1669,f494])).

fof(f1669,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1668,f1641])).

fof(f1668,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1653,f495])).

fof(f1653,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(trivial_inequality_removal,[],[f1650])).

fof(f1650,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(superposition,[],[f110,f1639])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1667,plain,
    ( ~ spl3_64
    | spl3_65
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f1658,f1596,f469,f368,f1664,f1660])).

fof(f1658,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1657,f494])).

fof(f1657,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1656,f1641])).

fof(f1656,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f1655,f495])).

fof(f1655,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(trivial_inequality_removal,[],[f1648])).

fof(f1648,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_funct_1(k1_xboole_0)
    | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_62 ),
    inference(superposition,[],[f112,f1639])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f1612,plain,
    ( spl3_63
    | spl3_62
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f1607,f469,f368,f1596,f1609])).

fof(f1607,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1606,f494])).

fof(f1606,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1587,f1560])).

fof(f1587,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(resolution,[],[f1578,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f1515,plain,
    ( ~ spl3_9
    | spl3_10
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f1514])).

fof(f1514,plain,
    ( $false
    | ~ spl3_9
    | spl3_10
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f1512,f636])).

fof(f636,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f635,f69])).

fof(f635,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f623,f613])).

fof(f613,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f612,f374])).

fof(f374,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f372])).

fof(f612,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f176,f196])).

fof(f196,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f623,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(resolution,[],[f615,f125])).

fof(f125,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f615,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f611,f374])).

fof(f611,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f178,f196])).

fof(f1512,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_10
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f208,f374])).

fof(f1451,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f1450])).

fof(f1450,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f1449,f77])).

fof(f77,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1449,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f1448,f149])).

fof(f149,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_3
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1448,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f1447,f69])).

fof(f1447,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f1435,f133])).

fof(f133,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1435,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_12 ),
    inference(equality_resolution,[],[f272])).

fof(f272,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_12
  <=> ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1370,plain,
    ( spl3_11
    | spl3_12
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1369,f159,f136,f271,f267])).

fof(f267,plain,
    ( spl3_11
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f136,plain,
    ( spl3_2
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f159,plain,
    ( spl3_5
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1369,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(sK2)
        | v2_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f1368,f138])).

fof(f138,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1368,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(sK2)
        | v2_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f868,f234])).

fof(f868,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(sK2)
        | v2_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_5 ),
    inference(superposition,[],[f91,f161])).

fof(f161,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f1337,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f1336])).

fof(f1336,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1332,f1013])).

fof(f1013,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1012,f69])).

fof(f1012,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1002,f992])).

fof(f992,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f963,f968])).

fof(f968,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f967,f133])).

fof(f967,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f966,f180])).

fof(f180,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f178,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f966,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(resolution,[],[f209,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f209,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f1002,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(resolution,[],[f990,f127])).

fof(f990,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f962,f968])).

fof(f1332,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f1100,f1314])).

fof(f1314,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1313,f173])).

fof(f173,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_7
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1313,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1312,f234])).

fof(f1312,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1311,f1059])).

fof(f1059,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1058,f69])).

fof(f1058,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1057,f992])).

fof(f1057,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1056,f990])).

fof(f1056,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1049,f73])).

fof(f1049,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f1046])).

fof(f1046,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f110,f1026])).

fof(f1026,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f964,f968])).

fof(f1311,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1310,f1063])).

fof(f1063,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1062,f69])).

fof(f1062,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1061,f992])).

fof(f1061,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1060,f990])).

fof(f1060,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1048,f73])).

fof(f1048,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f1047])).

fof(f1047,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f111,f1026])).

fof(f1310,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1309,f269])).

fof(f269,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f267])).

fof(f1309,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f1302])).

fof(f1302,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f112,f1121])).

fof(f1121,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1112,f167])).

fof(f167,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_6
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1112,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(resolution,[],[f1063,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1100,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f1066,f1055])).

fof(f1055,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1054,f69])).

fof(f1054,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1053,f992])).

fof(f1053,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1052,f990])).

fof(f1052,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1051,f73])).

fof(f1051,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f1044])).

fof(f1044,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f112,f1026])).

fof(f1066,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f965,f991])).

fof(f991,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f128,f968])).

fof(f714,plain,
    ( ~ spl3_9
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f713])).

fof(f713,plain,
    ( $false
    | ~ spl3_9
    | spl3_24 ),
    inference(subsumption_resolution,[],[f712,f196])).

fof(f712,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | ~ spl3_9
    | spl3_24 ),
    inference(forward_demodulation,[],[f471,f376])).

fof(f376,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f357,f245])).

fof(f245,plain,
    ( k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f218,f196])).

fof(f357,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f246,f98])).

fof(f246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f178,f196])).

fof(f471,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f469])).

fof(f608,plain,
    ( spl3_10
    | spl3_9 ),
    inference(avatar_split_clause,[],[f607,f194,f207])).

fof(f607,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f606,f69])).

fof(f606,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f595,f176])).

fof(f595,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f178,f126])).

fof(f493,plain,
    ( ~ spl3_1
    | ~ spl3_10
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f492])).

fof(f492,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_10
    | spl3_24 ),
    inference(subsumption_resolution,[],[f471,f455])).

fof(f455,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f428,f399])).

fof(f399,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f395,f98])).

fof(f395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f178,f387])).

fof(f387,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f386,f133])).

fof(f386,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f385,f180])).

fof(f385,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(resolution,[],[f209,f96])).

fof(f428,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f218,f387])).

fof(f375,plain,
    ( spl3_19
    | spl3_20
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f366,f194,f372,f368])).

fof(f366,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f356,f247])).

fof(f247,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f176,f196])).

fof(f356,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_9 ),
    inference(resolution,[],[f246,f120])).

fof(f315,plain,
    ( ~ spl3_15
    | spl3_17
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f310,f194,f312,f300])).

fof(f310,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f309,f69])).

fof(f309,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f308,f247])).

fof(f308,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f293,f73])).

fof(f293,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f290])).

fof(f290,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f110,f245])).

fof(f215,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f213,f92])).

fof(f92,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f213,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f187,f134])).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f187,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(resolution,[],[f178,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f174,plain,
    ( ~ spl3_1
    | spl3_7 ),
    inference(avatar_split_clause,[],[f169,f171,f132])).

fof(f169,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f144,f69])).

fof(f144,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f168,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f163,f165,f132])).

fof(f163,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f143,f69])).

fof(f143,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f162,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f157,f159,f132])).

fof(f157,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f142,f69])).

fof(f142,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f150,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f145,f147,f132])).

fof(f145,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f140,f69])).

fof(f140,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f139,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f130,f136,f132])).

fof(f130,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (27324)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (27332)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (27335)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (27342)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (27330)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (27320)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (27333)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (27334)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (27325)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (27329)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (27343)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (27326)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (27331)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (27340)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (27344)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (27322)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (27323)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (27327)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (27341)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (27321)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (27328)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (27337)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (27339)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (27338)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.52/0.56  % (27336)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.71/0.58  % (27345)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.71/0.63  % (27321)Refutation found. Thanks to Tanya!
% 1.71/0.63  % SZS status Theorem for theBenchmark
% 1.71/0.63  % SZS output start Proof for theBenchmark
% 1.71/0.63  fof(f2362,plain,(
% 1.71/0.63    $false),
% 1.71/0.63    inference(avatar_sat_refutation,[],[f139,f150,f162,f168,f174,f215,f315,f375,f493,f608,f714,f1337,f1370,f1451,f1515,f1612,f1667,f1675,f1683,f1779,f1782,f2274,f2341,f2354,f2361])).
% 1.71/0.63  fof(f2361,plain,(
% 1.71/0.63    ~spl3_19 | ~spl3_24 | ~spl3_62 | ~spl3_65 | ~spl3_75),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f2360])).
% 1.71/0.63  fof(f2360,plain,(
% 1.71/0.63    $false | (~spl3_19 | ~spl3_24 | ~spl3_62 | ~spl3_65 | ~spl3_75)),
% 1.71/0.63    inference(subsumption_resolution,[],[f2358,f1815])).
% 1.71/0.63  fof(f1815,plain,(
% 1.71/0.63    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1814,f494])).
% 1.71/0.63  fof(f494,plain,(
% 1.71/0.63    v1_funct_1(k1_xboole_0) | ~spl3_19),
% 1.71/0.63    inference(backward_demodulation,[],[f69,f370])).
% 1.71/0.63  fof(f370,plain,(
% 1.71/0.63    k1_xboole_0 = sK2 | ~spl3_19),
% 1.71/0.63    inference(avatar_component_clause,[],[f368])).
% 1.71/0.63  fof(f368,plain,(
% 1.71/0.63    spl3_19 <=> k1_xboole_0 = sK2),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.71/0.63  fof(f69,plain,(
% 1.71/0.63    v1_funct_1(sK2)),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f63,plain,(
% 1.71/0.63    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.71/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f62,f61,f60])).
% 1.71/0.63  fof(f60,plain,(
% 1.71/0.63    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 1.71/0.63    introduced(choice_axiom,[])).
% 1.71/0.63  fof(f61,plain,(
% 1.71/0.63    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 1.71/0.63    introduced(choice_axiom,[])).
% 1.71/0.63  fof(f62,plain,(
% 1.71/0.63    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.71/0.63    introduced(choice_axiom,[])).
% 1.71/0.63  fof(f27,plain,(
% 1.71/0.63    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.71/0.63    inference(flattening,[],[f26])).
% 1.71/0.63  fof(f26,plain,(
% 1.71/0.63    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.71/0.63    inference(ennf_transformation,[],[f24])).
% 1.71/0.63  fof(f24,plain,(
% 1.71/0.63    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.71/0.63    inference(pure_predicate_removal,[],[f23])).
% 1.71/0.63  fof(f23,negated_conjecture,(
% 1.71/0.63    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.71/0.63    inference(negated_conjecture,[],[f22])).
% 1.71/0.63  fof(f22,conjecture,(
% 1.71/0.63    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.71/0.63  fof(f1814,plain,(
% 1.71/0.63    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1805,f1641])).
% 1.71/0.63  fof(f1641,plain,(
% 1.71/0.63    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(backward_demodulation,[],[f1560,f1598])).
% 1.71/0.63  fof(f1598,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_62),
% 1.71/0.63    inference(avatar_component_clause,[],[f1596])).
% 1.71/0.63  fof(f1596,plain,(
% 1.71/0.63    spl3_62 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.71/0.63  fof(f1560,plain,(
% 1.71/0.63    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0)) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f963,f370])).
% 1.71/0.63  fof(f963,plain,(
% 1.71/0.63    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_24),
% 1.71/0.63    inference(forward_demodulation,[],[f176,f470])).
% 1.71/0.63  fof(f470,plain,(
% 1.71/0.63    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_24),
% 1.71/0.63    inference(avatar_component_clause,[],[f469])).
% 1.71/0.63  fof(f469,plain,(
% 1.71/0.63    spl3_24 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.71/0.63  fof(f176,plain,(
% 1.71/0.63    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.71/0.63    inference(forward_demodulation,[],[f175,f129])).
% 1.71/0.63  fof(f129,plain,(
% 1.71/0.63    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.71/0.63    inference(resolution,[],[f68,f78])).
% 1.71/0.63  fof(f78,plain,(
% 1.71/0.63    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f28])).
% 1.71/0.63  fof(f28,plain,(
% 1.71/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.71/0.63    inference(ennf_transformation,[],[f19])).
% 1.71/0.63  fof(f19,axiom,(
% 1.71/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.71/0.63  fof(f68,plain,(
% 1.71/0.63    l1_struct_0(sK1)),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f175,plain,(
% 1.71/0.63    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.71/0.63    inference(backward_demodulation,[],[f70,f128])).
% 1.71/0.63  fof(f128,plain,(
% 1.71/0.63    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.71/0.63    inference(resolution,[],[f67,f78])).
% 1.71/0.63  fof(f67,plain,(
% 1.71/0.63    l1_struct_0(sK0)),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f70,plain,(
% 1.71/0.63    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f1805,plain,(
% 1.71/0.63    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(resolution,[],[f1793,f127])).
% 1.71/0.63  fof(f127,plain,(
% 1.71/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.63    inference(duplicate_literal_removal,[],[f124])).
% 1.71/0.63  fof(f124,plain,(
% 1.71/0.63    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.63    inference(equality_resolution,[],[f116])).
% 1.71/0.63  fof(f116,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f66])).
% 1.71/0.63  fof(f66,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(nnf_transformation,[],[f59])).
% 1.71/0.63  fof(f59,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f58])).
% 1.71/0.63  fof(f58,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f14])).
% 1.71/0.63  fof(f14,axiom,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.71/0.63  fof(f1793,plain,(
% 1.71/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(forward_demodulation,[],[f1578,f1598])).
% 1.71/0.63  fof(f1578,plain,(
% 1.71/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0)))) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f962,f370])).
% 1.71/0.63  fof(f962,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_24),
% 1.71/0.63    inference(forward_demodulation,[],[f178,f470])).
% 1.71/0.63  fof(f178,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.71/0.63    inference(forward_demodulation,[],[f177,f128])).
% 1.71/0.63  fof(f177,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.71/0.63    inference(forward_demodulation,[],[f71,f129])).
% 1.71/0.63  fof(f71,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f2358,plain,(
% 1.71/0.63    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62 | ~spl3_65 | ~spl3_75)),
% 1.71/0.63    inference(backward_demodulation,[],[f1934,f2080])).
% 1.71/0.63  fof(f2080,plain,(
% 1.71/0.63    k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | ~spl3_75),
% 1.71/0.63    inference(avatar_component_clause,[],[f2078])).
% 1.71/0.63  fof(f2078,plain,(
% 1.71/0.63    spl3_75 <=> k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 1.71/0.63  fof(f1934,plain,(
% 1.71/0.63    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62 | ~spl3_65)),
% 1.71/0.63    inference(backward_demodulation,[],[f1858,f1666])).
% 1.71/0.63  fof(f1666,plain,(
% 1.71/0.63    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~spl3_65),
% 1.71/0.63    inference(avatar_component_clause,[],[f1664])).
% 1.71/0.63  fof(f1664,plain,(
% 1.71/0.63    spl3_65 <=> k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.71/0.63  fof(f1858,plain,(
% 1.71/0.63    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(forward_demodulation,[],[f1780,f1598])).
% 1.71/0.63  fof(f1780,plain,(
% 1.71/0.63    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f1706,f128])).
% 1.71/0.63  fof(f1706,plain,(
% 1.71/0.63    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f965,f370])).
% 1.71/0.63  fof(f965,plain,(
% 1.71/0.63    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~spl3_24),
% 1.71/0.63    inference(forward_demodulation,[],[f448,f470])).
% 1.71/0.63  fof(f448,plain,(
% 1.71/0.63    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.71/0.63    inference(forward_demodulation,[],[f74,f129])).
% 1.71/0.63  fof(f74,plain,(
% 1.71/0.63    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f2354,plain,(
% 1.71/0.63    ~spl3_19 | ~spl3_66 | ~spl3_67 | spl3_78),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f2353])).
% 1.71/0.63  fof(f2353,plain,(
% 1.71/0.63    $false | (~spl3_19 | ~spl3_66 | ~spl3_67 | spl3_78)),
% 1.71/0.63    inference(subsumption_resolution,[],[f2352,f504])).
% 1.71/0.63  fof(f504,plain,(
% 1.71/0.63    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl3_19),
% 1.71/0.63    inference(backward_demodulation,[],[f234,f370])).
% 1.71/0.63  fof(f234,plain,(
% 1.71/0.63    v1_funct_1(k2_funct_1(sK2))),
% 1.71/0.63    inference(subsumption_resolution,[],[f233,f69])).
% 1.71/0.63  fof(f233,plain,(
% 1.71/0.63    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f232,f176])).
% 1.71/0.63  fof(f232,plain,(
% 1.71/0.63    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f231,f178])).
% 1.71/0.63  fof(f231,plain,(
% 1.71/0.63    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f225,f73])).
% 1.71/0.63  fof(f73,plain,(
% 1.71/0.63    v2_funct_1(sK2)),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f225,plain,(
% 1.71/0.63    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f220])).
% 1.71/0.63  fof(f220,plain,(
% 1.71/0.63    k2_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(superposition,[],[f109,f218])).
% 1.71/0.63  fof(f218,plain,(
% 1.71/0.63    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.71/0.63    inference(forward_demodulation,[],[f217,f128])).
% 1.71/0.63  fof(f217,plain,(
% 1.71/0.63    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.71/0.63    inference(forward_demodulation,[],[f72,f129])).
% 1.71/0.63  fof(f72,plain,(
% 1.71/0.63    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.71/0.63    inference(cnf_transformation,[],[f63])).
% 1.71/0.63  fof(f109,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f53])).
% 1.71/0.63  fof(f53,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f52])).
% 1.71/0.63  fof(f52,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f16])).
% 1.71/0.63  fof(f16,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.71/0.63  fof(f2352,plain,(
% 1.71/0.63    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_66 | ~spl3_67 | spl3_78)),
% 1.71/0.63    inference(subsumption_resolution,[],[f2351,f1674])).
% 1.71/0.63  fof(f1674,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~spl3_66),
% 1.71/0.63    inference(avatar_component_clause,[],[f1672])).
% 1.71/0.63  fof(f1672,plain,(
% 1.71/0.63    spl3_66 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 1.71/0.63  fof(f2351,plain,(
% 1.71/0.63    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_67 | spl3_78)),
% 1.71/0.63    inference(subsumption_resolution,[],[f2350,f1682])).
% 1.71/0.63  fof(f1682,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl3_67),
% 1.71/0.63    inference(avatar_component_clause,[],[f1680])).
% 1.71/0.63  fof(f1680,plain,(
% 1.71/0.63    spl3_67 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 1.71/0.63  fof(f2350,plain,(
% 1.71/0.63    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | spl3_78),
% 1.71/0.63    inference(resolution,[],[f2273,f107])).
% 1.71/0.63  fof(f107,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f51])).
% 1.71/0.63  fof(f51,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f50])).
% 1.71/0.63  fof(f50,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f21])).
% 1.71/0.63  fof(f21,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 1.71/0.63  fof(f2273,plain,(
% 1.71/0.63    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | spl3_78),
% 1.71/0.63    inference(avatar_component_clause,[],[f2271])).
% 1.71/0.63  fof(f2271,plain,(
% 1.71/0.63    spl3_78 <=> v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 1.71/0.63  fof(f2341,plain,(
% 1.71/0.63    spl3_15 | ~spl3_19 | ~spl3_24 | ~spl3_62),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f2340])).
% 1.71/0.63  fof(f2340,plain,(
% 1.71/0.63    $false | (spl3_15 | ~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f2339,f1793])).
% 1.71/0.63  fof(f2339,plain,(
% 1.71/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (spl3_15 | ~spl3_19)),
% 1.71/0.63    inference(forward_demodulation,[],[f302,f370])).
% 1.71/0.63  fof(f302,plain,(
% 1.71/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | spl3_15),
% 1.71/0.63    inference(avatar_component_clause,[],[f300])).
% 1.71/0.63  fof(f300,plain,(
% 1.71/0.63    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.71/0.63  fof(f2274,plain,(
% 1.71/0.63    spl3_75 | ~spl3_78 | ~spl3_17 | ~spl3_19 | spl3_20 | ~spl3_67),
% 1.71/0.63    inference(avatar_split_clause,[],[f2269,f1680,f372,f368,f312,f2271,f2078])).
% 1.71/0.63  fof(f312,plain,(
% 1.71/0.63    spl3_17 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.71/0.63  fof(f372,plain,(
% 1.71/0.63    spl3_20 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.71/0.63  fof(f2269,plain,(
% 1.71/0.63    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_17 | ~spl3_19 | spl3_20 | ~spl3_67)),
% 1.71/0.63    inference(subsumption_resolution,[],[f2259,f373])).
% 1.71/0.63  fof(f373,plain,(
% 1.71/0.63    k1_xboole_0 != k2_struct_0(sK0) | spl3_20),
% 1.71/0.63    inference(avatar_component_clause,[],[f372])).
% 1.71/0.63  fof(f2259,plain,(
% 1.71/0.63    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_17 | ~spl3_19 | ~spl3_67)),
% 1.71/0.63    inference(resolution,[],[f1963,f120])).
% 1.71/0.63  fof(f120,plain,(
% 1.71/0.63    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.71/0.63    inference(equality_resolution,[],[f104])).
% 1.71/0.63  fof(f104,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f65])).
% 1.71/0.63  fof(f65,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(nnf_transformation,[],[f49])).
% 1.71/0.63  fof(f49,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(flattening,[],[f48])).
% 1.71/0.63  fof(f48,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f12])).
% 1.71/0.63  fof(f12,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.63  fof(f1963,plain,(
% 1.71/0.63    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_17 | ~spl3_19 | ~spl3_67)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1962,f504])).
% 1.71/0.63  fof(f1962,plain,(
% 1.71/0.63    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_17 | ~spl3_19 | ~spl3_67)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1951,f1717])).
% 1.71/0.63  fof(f1717,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | (~spl3_17 | ~spl3_19)),
% 1.71/0.63    inference(forward_demodulation,[],[f314,f370])).
% 1.71/0.63  fof(f314,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~spl3_17),
% 1.71/0.63    inference(avatar_component_clause,[],[f312])).
% 1.71/0.63  fof(f1951,plain,(
% 1.71/0.63    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl3_67),
% 1.71/0.63    inference(resolution,[],[f1682,f108])).
% 1.71/0.63  fof(f108,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f51])).
% 1.71/0.63  fof(f1782,plain,(
% 1.71/0.63    spl3_10 | ~spl3_19 | ~spl3_63),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f1781])).
% 1.71/0.63  fof(f1781,plain,(
% 1.71/0.63    $false | (spl3_10 | ~spl3_19 | ~spl3_63)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1611,f1580])).
% 1.71/0.63  fof(f1580,plain,(
% 1.71/0.63    ~v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | (spl3_10 | ~spl3_19)),
% 1.71/0.63    inference(forward_demodulation,[],[f208,f370])).
% 1.71/0.63  fof(f208,plain,(
% 1.71/0.63    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_10),
% 1.71/0.63    inference(avatar_component_clause,[],[f207])).
% 1.71/0.63  fof(f207,plain,(
% 1.71/0.63    spl3_10 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.71/0.63  fof(f1611,plain,(
% 1.71/0.63    v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | ~spl3_63),
% 1.71/0.63    inference(avatar_component_clause,[],[f1609])).
% 1.71/0.63  fof(f1609,plain,(
% 1.71/0.63    spl3_63 <=> v1_partfun1(k1_xboole_0,k2_struct_0(sK0))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 1.71/0.63  fof(f1779,plain,(
% 1.71/0.63    ~spl3_19 | ~spl3_24 | ~spl3_62 | spl3_64),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f1778])).
% 1.71/0.63  fof(f1778,plain,(
% 1.71/0.63    $false | (~spl3_19 | ~spl3_24 | ~spl3_62 | spl3_64)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1662,f1640])).
% 1.71/0.63  fof(f1640,plain,(
% 1.71/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(backward_demodulation,[],[f1578,f1598])).
% 1.71/0.63  fof(f1662,plain,(
% 1.71/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | spl3_64),
% 1.71/0.63    inference(avatar_component_clause,[],[f1660])).
% 1.71/0.63  fof(f1660,plain,(
% 1.71/0.63    spl3_64 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 1.71/0.63  fof(f1683,plain,(
% 1.71/0.63    ~spl3_64 | spl3_67 | ~spl3_19 | ~spl3_24 | ~spl3_62),
% 1.71/0.63    inference(avatar_split_clause,[],[f1678,f1596,f469,f368,f1680,f1660])).
% 1.71/0.63  fof(f1678,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1677,f494])).
% 1.71/0.63  fof(f1677,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1676,f1641])).
% 1.71/0.63  fof(f1676,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1652,f495])).
% 1.71/0.63  fof(f495,plain,(
% 1.71/0.63    v2_funct_1(k1_xboole_0) | ~spl3_19),
% 1.71/0.63    inference(backward_demodulation,[],[f73,f370])).
% 1.71/0.63  fof(f1652,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v2_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1651])).
% 1.71/0.63  fof(f1651,plain,(
% 1.71/0.63    k1_xboole_0 != k1_xboole_0 | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v2_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(superposition,[],[f111,f1639])).
% 1.71/0.63  fof(f1639,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(backward_demodulation,[],[f1617,f1598])).
% 1.71/0.63  fof(f1617,plain,(
% 1.71/0.63    k2_relat_1(k1_xboole_0) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f964,f370])).
% 1.71/0.63  fof(f964,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_24),
% 1.71/0.63    inference(forward_demodulation,[],[f218,f470])).
% 1.71/0.63  fof(f111,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f53])).
% 1.71/0.63  fof(f1675,plain,(
% 1.71/0.63    ~spl3_64 | spl3_66 | ~spl3_19 | ~spl3_24 | ~spl3_62),
% 1.71/0.63    inference(avatar_split_clause,[],[f1670,f1596,f469,f368,f1672,f1660])).
% 1.71/0.63  fof(f1670,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1669,f494])).
% 1.71/0.63  fof(f1669,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1668,f1641])).
% 1.71/0.63  fof(f1668,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1653,f495])).
% 1.71/0.63  fof(f1653,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1650])).
% 1.71/0.63  fof(f1650,plain,(
% 1.71/0.63    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(superposition,[],[f110,f1639])).
% 1.71/0.63  fof(f110,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f53])).
% 1.71/0.63  fof(f1667,plain,(
% 1.71/0.63    ~spl3_64 | spl3_65 | ~spl3_19 | ~spl3_24 | ~spl3_62),
% 1.71/0.63    inference(avatar_split_clause,[],[f1658,f1596,f469,f368,f1664,f1660])).
% 1.71/0.63  fof(f1658,plain,(
% 1.71/0.63    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1657,f494])).
% 1.71/0.63  fof(f1657,plain,(
% 1.71/0.63    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1656,f1641])).
% 1.71/0.63  fof(f1656,plain,(
% 1.71/0.63    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1655,f495])).
% 1.71/0.63  fof(f1655,plain,(
% 1.71/0.63    ~v2_funct_1(k1_xboole_0) | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1648])).
% 1.71/0.63  fof(f1648,plain,(
% 1.71/0.63    k1_xboole_0 != k1_xboole_0 | ~v2_funct_1(k1_xboole_0) | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24 | ~spl3_62)),
% 1.71/0.63    inference(superposition,[],[f112,f1639])).
% 1.71/0.63  fof(f112,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f55])).
% 1.71/0.63  fof(f55,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f54])).
% 1.71/0.63  fof(f54,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f20])).
% 1.71/0.63  fof(f20,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.71/0.63  fof(f1612,plain,(
% 1.71/0.63    spl3_63 | spl3_62 | ~spl3_19 | ~spl3_24),
% 1.71/0.63    inference(avatar_split_clause,[],[f1607,f469,f368,f1596,f1609])).
% 1.71/0.63  fof(f1607,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1606,f494])).
% 1.71/0.63  fof(f1606,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1587,f1560])).
% 1.71/0.63  fof(f1587,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | (~spl3_19 | ~spl3_24)),
% 1.71/0.63    inference(resolution,[],[f1578,f126])).
% 1.71/0.63  fof(f126,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(duplicate_literal_removal,[],[f113])).
% 1.71/0.63  fof(f113,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f57])).
% 1.71/0.63  fof(f57,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f56])).
% 1.71/0.63  fof(f56,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f15])).
% 1.71/0.63  fof(f15,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 1.71/0.63  fof(f1515,plain,(
% 1.71/0.63    ~spl3_9 | spl3_10 | ~spl3_20),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f1514])).
% 1.71/0.63  fof(f1514,plain,(
% 1.71/0.63    $false | (~spl3_9 | spl3_10 | ~spl3_20)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1512,f636])).
% 1.71/0.63  fof(f636,plain,(
% 1.71/0.63    v1_partfun1(sK2,k1_xboole_0) | (~spl3_9 | ~spl3_20)),
% 1.71/0.63    inference(subsumption_resolution,[],[f635,f69])).
% 1.71/0.63  fof(f635,plain,(
% 1.71/0.63    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | (~spl3_9 | ~spl3_20)),
% 1.71/0.63    inference(subsumption_resolution,[],[f623,f613])).
% 1.71/0.63  fof(f613,plain,(
% 1.71/0.63    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_9 | ~spl3_20)),
% 1.71/0.63    inference(backward_demodulation,[],[f612,f374])).
% 1.71/0.63  fof(f374,plain,(
% 1.71/0.63    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_20),
% 1.71/0.63    inference(avatar_component_clause,[],[f372])).
% 1.71/0.63  fof(f612,plain,(
% 1.71/0.63    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_9),
% 1.71/0.63    inference(backward_demodulation,[],[f176,f196])).
% 1.71/0.63  fof(f196,plain,(
% 1.71/0.63    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_9),
% 1.71/0.63    inference(avatar_component_clause,[],[f194])).
% 1.71/0.63  fof(f194,plain,(
% 1.71/0.63    spl3_9 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.71/0.63  fof(f623,plain,(
% 1.71/0.63    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (~spl3_9 | ~spl3_20)),
% 1.71/0.63    inference(resolution,[],[f615,f125])).
% 1.71/0.63  fof(f125,plain,(
% 1.71/0.63    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(duplicate_literal_removal,[],[f123])).
% 1.71/0.63  fof(f123,plain,(
% 1.71/0.63    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(equality_resolution,[],[f114])).
% 1.71/0.63  fof(f114,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f57])).
% 1.71/0.63  fof(f615,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_9 | ~spl3_20)),
% 1.71/0.63    inference(forward_demodulation,[],[f611,f374])).
% 1.71/0.63  fof(f611,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_9),
% 1.71/0.63    inference(backward_demodulation,[],[f178,f196])).
% 1.71/0.63  fof(f1512,plain,(
% 1.71/0.63    ~v1_partfun1(sK2,k1_xboole_0) | (spl3_10 | ~spl3_20)),
% 1.71/0.63    inference(backward_demodulation,[],[f208,f374])).
% 1.71/0.63  fof(f1451,plain,(
% 1.71/0.63    ~spl3_1 | ~spl3_3 | ~spl3_12),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f1450])).
% 1.71/0.63  fof(f1450,plain,(
% 1.71/0.63    $false | (~spl3_1 | ~spl3_3 | ~spl3_12)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1449,f77])).
% 1.71/0.63  fof(f77,plain,(
% 1.71/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f5])).
% 1.71/0.63  fof(f5,axiom,(
% 1.71/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.71/0.63  fof(f1449,plain,(
% 1.71/0.63    ~v2_funct_1(k6_relat_1(k1_relat_1(sK2))) | (~spl3_1 | ~spl3_3 | ~spl3_12)),
% 1.71/0.63    inference(forward_demodulation,[],[f1448,f149])).
% 1.71/0.63  fof(f149,plain,(
% 1.71/0.63    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_3),
% 1.71/0.63    inference(avatar_component_clause,[],[f147])).
% 1.71/0.63  fof(f147,plain,(
% 1.71/0.63    spl3_3 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.71/0.63  fof(f1448,plain,(
% 1.71/0.63    ~v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) | (~spl3_1 | ~spl3_12)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1447,f69])).
% 1.71/0.63  fof(f1447,plain,(
% 1.71/0.63    ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) | (~spl3_1 | ~spl3_12)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1435,f133])).
% 1.71/0.63  fof(f133,plain,(
% 1.71/0.63    v1_relat_1(sK2) | ~spl3_1),
% 1.71/0.63    inference(avatar_component_clause,[],[f132])).
% 1.71/0.63  fof(f132,plain,(
% 1.71/0.63    spl3_1 <=> v1_relat_1(sK2)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.71/0.63  fof(f1435,plain,(
% 1.71/0.63    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl3_12),
% 1.71/0.63    inference(equality_resolution,[],[f272])).
% 1.71/0.63  fof(f272,plain,(
% 1.71/0.63    ( ! [X1] : (k2_relat_1(X1) != k2_relat_1(sK2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))) ) | ~spl3_12),
% 1.71/0.63    inference(avatar_component_clause,[],[f271])).
% 1.71/0.63  fof(f271,plain,(
% 1.71/0.63    spl3_12 <=> ! [X1] : (k2_relat_1(X1) != k2_relat_1(sK2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.71/0.63  fof(f1370,plain,(
% 1.71/0.63    spl3_11 | spl3_12 | ~spl3_2 | ~spl3_5),
% 1.71/0.63    inference(avatar_split_clause,[],[f1369,f159,f136,f271,f267])).
% 1.71/0.63  fof(f267,plain,(
% 1.71/0.63    spl3_11 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.71/0.63  fof(f136,plain,(
% 1.71/0.63    spl3_2 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.71/0.63  fof(f159,plain,(
% 1.71/0.63    spl3_5 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.71/0.63  fof(f1369,plain,(
% 1.71/0.63    ( ! [X1] : (k2_relat_1(X1) != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl3_2 | ~spl3_5)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1368,f138])).
% 1.71/0.63  fof(f138,plain,(
% 1.71/0.63    v1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 1.71/0.63    inference(avatar_component_clause,[],[f136])).
% 1.71/0.63  fof(f1368,plain,(
% 1.71/0.63    ( ! [X1] : (k2_relat_1(X1) != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_5),
% 1.71/0.63    inference(subsumption_resolution,[],[f868,f234])).
% 1.71/0.63  fof(f868,plain,(
% 1.71/0.63    ( ! [X1] : (k2_relat_1(X1) != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_5),
% 1.71/0.63    inference(superposition,[],[f91,f161])).
% 1.71/0.63  fof(f161,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.71/0.63    inference(avatar_component_clause,[],[f159])).
% 1.71/0.63  fof(f91,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f41])).
% 1.71/0.63  fof(f41,plain,(
% 1.71/0.63    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.63    inference(flattening,[],[f40])).
% 1.71/0.63  fof(f40,plain,(
% 1.71/0.63    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.63    inference(ennf_transformation,[],[f6])).
% 1.71/0.63  fof(f6,axiom,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.71/0.63  fof(f1337,plain,(
% 1.71/0.63    ~spl3_1 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_24),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f1336])).
% 1.71/0.63  fof(f1336,plain,(
% 1.71/0.63    $false | (~spl3_1 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1332,f1013])).
% 1.71/0.63  fof(f1013,plain,(
% 1.71/0.63    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1012,f69])).
% 1.71/0.63  fof(f1012,plain,(
% 1.71/0.63    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1002,f992])).
% 1.71/0.63  fof(f992,plain,(
% 1.71/0.63    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(backward_demodulation,[],[f963,f968])).
% 1.71/0.63  fof(f968,plain,(
% 1.71/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(subsumption_resolution,[],[f967,f133])).
% 1.71/0.63  fof(f967,plain,(
% 1.71/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_10),
% 1.71/0.63    inference(subsumption_resolution,[],[f966,f180])).
% 1.71/0.63  fof(f180,plain,(
% 1.71/0.63    v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.71/0.63    inference(resolution,[],[f178,f99])).
% 1.71/0.63  fof(f99,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f47])).
% 1.71/0.63  fof(f47,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f25])).
% 1.71/0.63  fof(f25,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.71/0.63    inference(pure_predicate_removal,[],[f10])).
% 1.71/0.63  fof(f10,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.63  fof(f966,plain,(
% 1.71/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_10),
% 1.71/0.63    inference(resolution,[],[f209,f96])).
% 1.71/0.63  fof(f96,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f64])).
% 1.71/0.63  fof(f64,plain,(
% 1.71/0.63    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.63    inference(nnf_transformation,[],[f45])).
% 1.71/0.63  fof(f45,plain,(
% 1.71/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.63    inference(flattening,[],[f44])).
% 1.71/0.63  fof(f44,plain,(
% 1.71/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.71/0.63    inference(ennf_transformation,[],[f13])).
% 1.71/0.63  fof(f13,axiom,(
% 1.71/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.71/0.63  fof(f209,plain,(
% 1.71/0.63    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_10),
% 1.71/0.63    inference(avatar_component_clause,[],[f207])).
% 1.71/0.63  fof(f1002,plain,(
% 1.71/0.63    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(resolution,[],[f990,f127])).
% 1.71/0.63  fof(f990,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(backward_demodulation,[],[f962,f968])).
% 1.71/0.63  fof(f1332,plain,(
% 1.71/0.63    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_1 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(backward_demodulation,[],[f1100,f1314])).
% 1.71/0.63  fof(f1314,plain,(
% 1.71/0.63    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f1313,f173])).
% 1.71/0.63  fof(f173,plain,(
% 1.71/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_7),
% 1.71/0.63    inference(avatar_component_clause,[],[f171])).
% 1.71/0.63  fof(f171,plain,(
% 1.71/0.63    spl3_7 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.71/0.63  fof(f1313,plain,(
% 1.71/0.63    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1312,f234])).
% 1.71/0.63  fof(f1312,plain,(
% 1.71/0.63    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1311,f1059])).
% 1.71/0.63  fof(f1059,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1058,f69])).
% 1.71/0.63  fof(f1058,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1057,f992])).
% 1.71/0.63  fof(f1057,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1056,f990])).
% 1.71/0.63  fof(f1056,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1049,f73])).
% 1.71/0.63  fof(f1049,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1046])).
% 1.71/0.63  fof(f1046,plain,(
% 1.71/0.63    k2_relat_1(sK2) != k2_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(superposition,[],[f110,f1026])).
% 1.71/0.63  fof(f1026,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f964,f968])).
% 1.71/0.63  fof(f1311,plain,(
% 1.71/0.63    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1310,f1063])).
% 1.71/0.63  fof(f1063,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1062,f69])).
% 1.71/0.63  fof(f1062,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1061,f992])).
% 1.71/0.63  fof(f1061,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1060,f990])).
% 1.71/0.63  fof(f1060,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1048,f73])).
% 1.71/0.63  fof(f1048,plain,(
% 1.71/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1047])).
% 1.71/0.63  fof(f1047,plain,(
% 1.71/0.63    k2_relat_1(sK2) != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(superposition,[],[f111,f1026])).
% 1.71/0.63  fof(f1310,plain,(
% 1.71/0.63    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_11 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1309,f269])).
% 1.71/0.63  fof(f269,plain,(
% 1.71/0.63    v2_funct_1(k2_funct_1(sK2)) | ~spl3_11),
% 1.71/0.63    inference(avatar_component_clause,[],[f267])).
% 1.71/0.63  fof(f1309,plain,(
% 1.71/0.63    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1302])).
% 1.71/0.63  fof(f1302,plain,(
% 1.71/0.63    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(superposition,[],[f112,f1121])).
% 1.71/0.63  fof(f1121,plain,(
% 1.71/0.63    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f1112,f167])).
% 1.71/0.63  fof(f167,plain,(
% 1.71/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 1.71/0.63    inference(avatar_component_clause,[],[f165])).
% 1.71/0.63  fof(f165,plain,(
% 1.71/0.63    spl3_6 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.71/0.63  fof(f1112,plain,(
% 1.71/0.63    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(resolution,[],[f1063,f98])).
% 1.71/0.63  fof(f98,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f46])).
% 1.71/0.63  fof(f46,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f11])).
% 1.71/0.63  fof(f11,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.71/0.63  fof(f1100,plain,(
% 1.71/0.63    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(backward_demodulation,[],[f1066,f1055])).
% 1.71/0.63  fof(f1055,plain,(
% 1.71/0.63    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1054,f69])).
% 1.71/0.63  fof(f1054,plain,(
% 1.71/0.63    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1053,f992])).
% 1.71/0.63  fof(f1053,plain,(
% 1.71/0.63    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1052,f990])).
% 1.71/0.63  fof(f1052,plain,(
% 1.71/0.63    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1051,f73])).
% 1.71/0.63  fof(f1051,plain,(
% 1.71/0.63    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f1044])).
% 1.71/0.63  fof(f1044,plain,(
% 1.71/0.63    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(superposition,[],[f112,f1026])).
% 1.71/0.63  fof(f1066,plain,(
% 1.71/0.63    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (~spl3_1 | ~spl3_10 | ~spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f965,f991])).
% 1.71/0.63  fof(f991,plain,(
% 1.71/0.63    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(backward_demodulation,[],[f128,f968])).
% 1.71/0.63  fof(f714,plain,(
% 1.71/0.63    ~spl3_9 | spl3_24),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f713])).
% 1.71/0.63  fof(f713,plain,(
% 1.71/0.63    $false | (~spl3_9 | spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f712,f196])).
% 1.71/0.63  fof(f712,plain,(
% 1.71/0.63    k1_xboole_0 != k2_struct_0(sK1) | (~spl3_9 | spl3_24)),
% 1.71/0.63    inference(forward_demodulation,[],[f471,f376])).
% 1.71/0.63  fof(f376,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_9),
% 1.71/0.63    inference(forward_demodulation,[],[f357,f245])).
% 1.71/0.63  fof(f245,plain,(
% 1.71/0.63    k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_9),
% 1.71/0.63    inference(backward_demodulation,[],[f218,f196])).
% 1.71/0.63  fof(f357,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_9),
% 1.71/0.63    inference(resolution,[],[f246,f98])).
% 1.71/0.63  fof(f246,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_9),
% 1.71/0.63    inference(backward_demodulation,[],[f178,f196])).
% 1.71/0.63  fof(f471,plain,(
% 1.71/0.63    k2_struct_0(sK1) != k2_relat_1(sK2) | spl3_24),
% 1.71/0.63    inference(avatar_component_clause,[],[f469])).
% 1.71/0.63  fof(f608,plain,(
% 1.71/0.63    spl3_10 | spl3_9),
% 1.71/0.63    inference(avatar_split_clause,[],[f607,f194,f207])).
% 1.71/0.63  fof(f607,plain,(
% 1.71/0.63    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.71/0.63    inference(subsumption_resolution,[],[f606,f69])).
% 1.71/0.63  fof(f606,plain,(
% 1.71/0.63    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f595,f176])).
% 1.71/0.63  fof(f595,plain,(
% 1.71/0.63    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.71/0.63    inference(resolution,[],[f178,f126])).
% 1.71/0.63  fof(f493,plain,(
% 1.71/0.63    ~spl3_1 | ~spl3_10 | spl3_24),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f492])).
% 1.71/0.63  fof(f492,plain,(
% 1.71/0.63    $false | (~spl3_1 | ~spl3_10 | spl3_24)),
% 1.71/0.63    inference(subsumption_resolution,[],[f471,f455])).
% 1.71/0.63  fof(f455,plain,(
% 1.71/0.63    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(backward_demodulation,[],[f428,f399])).
% 1.71/0.63  fof(f399,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(resolution,[],[f395,f98])).
% 1.71/0.63  fof(f395,plain,(
% 1.71/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(forward_demodulation,[],[f178,f387])).
% 1.71/0.63  fof(f387,plain,(
% 1.71/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(subsumption_resolution,[],[f386,f133])).
% 1.71/0.63  fof(f386,plain,(
% 1.71/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_10),
% 1.71/0.63    inference(subsumption_resolution,[],[f385,f180])).
% 1.71/0.63  fof(f385,plain,(
% 1.71/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_10),
% 1.71/0.63    inference(resolution,[],[f209,f96])).
% 1.71/0.63  fof(f428,plain,(
% 1.71/0.63    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_10)),
% 1.71/0.63    inference(forward_demodulation,[],[f218,f387])).
% 1.71/0.63  fof(f375,plain,(
% 1.71/0.63    spl3_19 | spl3_20 | ~spl3_9),
% 1.71/0.63    inference(avatar_split_clause,[],[f366,f194,f372,f368])).
% 1.71/0.63  fof(f366,plain,(
% 1.71/0.63    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_9),
% 1.71/0.63    inference(subsumption_resolution,[],[f356,f247])).
% 1.71/0.63  fof(f247,plain,(
% 1.71/0.63    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_9),
% 1.71/0.63    inference(backward_demodulation,[],[f176,f196])).
% 1.71/0.63  fof(f356,plain,(
% 1.71/0.63    ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_9),
% 1.71/0.63    inference(resolution,[],[f246,f120])).
% 1.71/0.63  fof(f315,plain,(
% 1.71/0.63    ~spl3_15 | spl3_17 | ~spl3_9),
% 1.71/0.63    inference(avatar_split_clause,[],[f310,f194,f312,f300])).
% 1.71/0.63  fof(f310,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_9),
% 1.71/0.63    inference(subsumption_resolution,[],[f309,f69])).
% 1.71/0.63  fof(f309,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(sK2) | ~spl3_9),
% 1.71/0.63    inference(subsumption_resolution,[],[f308,f247])).
% 1.71/0.63  fof(f308,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_9),
% 1.71/0.63    inference(subsumption_resolution,[],[f293,f73])).
% 1.71/0.63  fof(f293,plain,(
% 1.71/0.63    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_9),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f290])).
% 1.71/0.63  fof(f290,plain,(
% 1.71/0.63    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_9),
% 1.71/0.63    inference(superposition,[],[f110,f245])).
% 1.71/0.63  fof(f215,plain,(
% 1.71/0.63    spl3_1),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f214])).
% 1.71/0.63  fof(f214,plain,(
% 1.71/0.63    $false | spl3_1),
% 1.71/0.63    inference(subsumption_resolution,[],[f213,f92])).
% 1.71/0.63  fof(f92,plain,(
% 1.71/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f3])).
% 1.71/0.63  fof(f3,axiom,(
% 1.71/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.63  fof(f213,plain,(
% 1.71/0.63    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_1),
% 1.71/0.63    inference(subsumption_resolution,[],[f187,f134])).
% 1.71/0.63  fof(f134,plain,(
% 1.71/0.63    ~v1_relat_1(sK2) | spl3_1),
% 1.71/0.63    inference(avatar_component_clause,[],[f132])).
% 1.71/0.63  fof(f187,plain,(
% 1.71/0.63    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 1.71/0.63    inference(resolution,[],[f178,f79])).
% 1.71/0.63  fof(f79,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f29])).
% 1.71/0.63  fof(f29,plain,(
% 1.71/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.63    inference(ennf_transformation,[],[f2])).
% 1.71/0.63  fof(f2,axiom,(
% 1.71/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.63  fof(f174,plain,(
% 1.71/0.63    ~spl3_1 | spl3_7),
% 1.71/0.63    inference(avatar_split_clause,[],[f169,f171,f132])).
% 1.71/0.63  fof(f169,plain,(
% 1.71/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f144,f69])).
% 1.71/0.63  fof(f144,plain,(
% 1.71/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(resolution,[],[f73,f85])).
% 1.71/0.63  fof(f85,plain,(
% 1.71/0.63    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f35])).
% 1.71/0.63  fof(f35,plain,(
% 1.71/0.63    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.63    inference(flattening,[],[f34])).
% 1.71/0.63  fof(f34,plain,(
% 1.71/0.63    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.63    inference(ennf_transformation,[],[f9])).
% 1.71/0.63  fof(f9,axiom,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.71/0.63  fof(f168,plain,(
% 1.71/0.63    ~spl3_1 | spl3_6),
% 1.71/0.63    inference(avatar_split_clause,[],[f163,f165,f132])).
% 1.71/0.63  fof(f163,plain,(
% 1.71/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f143,f69])).
% 1.71/0.63  fof(f143,plain,(
% 1.71/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(resolution,[],[f73,f87])).
% 1.71/0.63  fof(f87,plain,(
% 1.71/0.63    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f37])).
% 1.71/0.63  fof(f37,plain,(
% 1.71/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.63    inference(flattening,[],[f36])).
% 1.71/0.63  fof(f36,plain,(
% 1.71/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.63    inference(ennf_transformation,[],[f7])).
% 1.71/0.63  fof(f7,axiom,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.71/0.63  fof(f162,plain,(
% 1.71/0.63    ~spl3_1 | spl3_5),
% 1.71/0.63    inference(avatar_split_clause,[],[f157,f159,f132])).
% 1.71/0.63  fof(f157,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f142,f69])).
% 1.71/0.63  fof(f142,plain,(
% 1.71/0.63    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(resolution,[],[f73,f86])).
% 1.71/0.63  fof(f86,plain,(
% 1.71/0.63    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f37])).
% 1.71/0.63  fof(f150,plain,(
% 1.71/0.63    ~spl3_1 | spl3_3),
% 1.71/0.63    inference(avatar_split_clause,[],[f145,f147,f132])).
% 1.71/0.63  fof(f145,plain,(
% 1.71/0.63    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(subsumption_resolution,[],[f140,f69])).
% 1.71/0.63  fof(f140,plain,(
% 1.71/0.63    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(resolution,[],[f73,f88])).
% 1.71/0.63  fof(f88,plain,(
% 1.71/0.63    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f39])).
% 1.71/0.63  fof(f39,plain,(
% 1.71/0.63    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.63    inference(flattening,[],[f38])).
% 1.71/0.63  fof(f38,plain,(
% 1.71/0.63    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.63    inference(ennf_transformation,[],[f8])).
% 1.71/0.63  fof(f8,axiom,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.71/0.63  fof(f139,plain,(
% 1.71/0.63    ~spl3_1 | spl3_2),
% 1.71/0.63    inference(avatar_split_clause,[],[f130,f136,f132])).
% 1.71/0.63  fof(f130,plain,(
% 1.71/0.63    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.71/0.63    inference(resolution,[],[f69,f83])).
% 1.71/0.63  fof(f83,plain,(
% 1.71/0.63    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f33])).
% 1.71/0.63  fof(f33,plain,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.63    inference(flattening,[],[f32])).
% 1.71/0.63  fof(f32,plain,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.63    inference(ennf_transformation,[],[f4])).
% 1.71/0.63  fof(f4,axiom,(
% 1.71/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.71/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.71/0.63  % SZS output end Proof for theBenchmark
% 1.71/0.63  % (27321)------------------------------
% 1.71/0.63  % (27321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.63  % (27321)Termination reason: Refutation
% 1.71/0.63  
% 1.71/0.63  % (27321)Memory used [KB]: 11385
% 1.71/0.63  % (27321)Time elapsed: 0.228 s
% 1.71/0.63  % (27321)------------------------------
% 1.71/0.63  % (27321)------------------------------
% 2.17/0.64  % (27315)Success in time 0.276 s
%------------------------------------------------------------------------------
