%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:53 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 502 expanded)
%              Number of leaves         :   48 ( 198 expanded)
%              Depth                    :   17
%              Number of atoms          :  780 (1749 expanded)
%              Number of equality atoms :   80 ( 169 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2928,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f154,f185,f226,f235,f251,f310,f356,f361,f585,f618,f626,f647,f656,f661,f1010,f1056,f1074,f1144,f1266,f1589,f1679,f1680,f1778,f2054,f2063,f2078,f2382,f2895,f2922,f2927])).

fof(f2927,plain,
    ( u1_struct_0(sK2) != u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2922,plain,
    ( ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_37
    | ~ spl7_43
    | ~ spl7_77
    | ~ spl7_92
    | ~ spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2921])).

fof(f2921,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_37
    | ~ spl7_43
    | ~ spl7_77
    | ~ spl7_92
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f2920,f124])).

fof(f124,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f73,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f2920,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_37
    | ~ spl7_43
    | ~ spl7_77
    | ~ spl7_92
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f2919,f2067])).

fof(f2067,plain,
    ( sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f2065])).

fof(f2065,plain,
    ( spl7_95
  <=> sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f2919,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_37
    | ~ spl7_43
    | ~ spl7_77
    | ~ spl7_92
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f2904,f2918])).

fof(f2918,plain,
    ( ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_37
    | ~ spl7_77
    | ~ spl7_92
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f2897,f2917])).

fof(f2917,plain,
    ( v2_compts_1(sK3,sK2)
    | ~ spl7_2
    | ~ spl7_37
    | ~ spl7_77
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f2916,f124])).

fof(f2916,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | v2_compts_1(sK3,sK2)
    | ~ spl7_2
    | ~ spl7_37
    | ~ spl7_77
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f2905,f2067])).

fof(f2905,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
    | v2_compts_1(sK3,sK2)
    | ~ spl7_2
    | ~ spl7_37
    | ~ spl7_77 ),
    inference(resolution,[],[f1773,f1627])).

fof(f1627,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X1,sK2) )
    | ~ spl7_2
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1623,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_2
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1623,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X1,sK2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl7_37 ),
    inference(resolution,[],[f625,f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f119,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(f625,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl7_37
  <=> m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f1773,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f1771,plain,
    ( spl7_77
  <=> v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f2897,plain,
    ( ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_compts_1(sK3,sK2)
    | ~ spl7_6
    | ~ spl7_92 ),
    inference(subsumption_resolution,[],[f2896,f160])).

fof(f160,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f2896,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_compts_1(sK3,sK2)
    | ~ spl7_6
    | ~ spl7_92 ),
    inference(forward_demodulation,[],[f1591,f2053])).

fof(f2053,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f2051])).

fof(f2051,plain,
    ( spl7_92
  <=> u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f1591,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_compts_1(sK3,sK2)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f72,f160])).

fof(f72,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_compts_1(sK3,sK2) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        & v2_compts_1(sK3,sK2) ) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v2_compts_1(X1,sK2) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
              & v2_compts_1(X1,sK2) ) ) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v2_compts_1(X1,sK2) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            & v2_compts_1(X1,sK2) ) ) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v2_compts_1(sK3,sK2) )
      & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
          & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
        | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
          & v2_compts_1(sK3,sK2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

fof(f2904,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
    | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_16
    | ~ spl7_43
    | ~ spl7_77 ),
    inference(resolution,[],[f1773,f1740])).

fof(f1740,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl7_16
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f1735,f355])).

fof(f355,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl7_16
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1735,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl7_43 ),
    inference(resolution,[],[f724,f125])).

fof(f724,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl7_43
  <=> m1_pre_topc(k1_pre_topc(sK2,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f2895,plain,
    ( spl7_77
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_43
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f2835,f2065,f723,f353,f151,f1771])).

fof(f151,plain,
    ( spl7_5
  <=> v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f2835,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3))
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_43
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f2834,f124])).

fof(f2834,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3))
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_43
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f2833,f2067])).

fof(f2833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3))
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_43 ),
    inference(resolution,[],[f1739,f153])).

fof(f153,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1739,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) )
    | ~ spl7_16
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f1734,f355])).

fof(f1734,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X0,k1_pre_topc(sK2,sK3))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl7_43 ),
    inference(resolution,[],[f724,f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X3,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f120,f101])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2382,plain,
    ( spl7_78
    | ~ spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2381])).

fof(f2381,plain,
    ( $false
    | spl7_78
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f2347,f124])).

fof(f2347,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | spl7_78
    | ~ spl7_95 ),
    inference(superposition,[],[f1777,f2067])).

fof(f1777,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
    | spl7_78 ),
    inference(avatar_component_clause,[],[f1775])).

fof(f1775,plain,
    ( spl7_78
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f2078,plain,
    ( spl7_95
    | ~ spl7_39
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f2072,f2060,f644,f2065])).

fof(f644,plain,
    ( spl7_39
  <=> sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f2060,plain,
    ( spl7_94
  <=> u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f2072,plain,
    ( sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_39
    | ~ spl7_94 ),
    inference(forward_demodulation,[],[f2062,f646])).

fof(f646,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f644])).

fof(f2062,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f2060])).

fof(f2063,plain,
    ( spl7_94
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f1316,f1071,f2060])).

fof(f1071,plain,
    ( spl7_51
  <=> l1_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f1316,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_51 ),
    inference(resolution,[],[f1073,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1073,plain,
    ( l1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f2054,plain,
    ( spl7_92
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f1270,f1263,f1141,f2051])).

fof(f1141,plain,
    ( spl7_55
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f1263,plain,
    ( spl7_60
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f1270,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f1143,f1265,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f1265,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f1143,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f1778,plain,
    ( spl7_77
    | ~ spl7_78
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f1703,f623,f147,f134,f1775,f1771])).

fof(f147,plain,
    ( spl7_4
  <=> v2_compts_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1703,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_37 ),
    inference(resolution,[],[f1626,f149])).

fof(f149,plain,
    ( v2_compts_1(sK3,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1626,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) )
    | ~ spl7_2
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1622,f136])).

fof(f1622,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))
        | v2_compts_1(X0,k1_pre_topc(sK2,sK3))
        | ~ l1_pre_topc(sK2) )
    | ~ spl7_37 ),
    inference(resolution,[],[f625,f126])).

fof(f1680,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != k1_pre_topc(sK2,sK3)
    | m1_pre_topc(k1_pre_topc(sK2,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1679,plain,
    ( spl7_71
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_41
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f1614,f1263,f1141,f653,f158,f134,f1676])).

fof(f1676,plain,
    ( spl7_71
  <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = k1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f653,plain,
    ( spl7_41
  <=> k1_pre_topc(sK2,sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f1614,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = k1_pre_topc(sK2,sK3)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_41
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(forward_demodulation,[],[f1613,f655])).

fof(f655,plain,
    ( k1_pre_topc(sK2,sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f653])).

fof(f1613,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f1612,f160])).

fof(f1612,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(forward_demodulation,[],[f1607,f1270])).

fof(f1607,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f160,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,X0)),u1_pre_topc(k1_pre_topc(sK2,X0))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f121,f136])).

fof(f121,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

fof(f1589,plain,
    ( ~ spl7_6
    | spl7_8
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(avatar_contradiction_clause,[],[f1588])).

fof(f1588,plain,
    ( $false
    | ~ spl7_6
    | spl7_8
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f1585,f160])).

fof(f1585,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_8
    | ~ spl7_55
    | ~ spl7_60 ),
    inference(forward_demodulation,[],[f169,f1270])).

fof(f169,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1266,plain,
    ( spl7_60
    | ~ spl7_16
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f382,f358,f353,f1263])).

fof(f358,plain,
    ( spl7_17
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f382,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl7_16
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f355,f360,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f360,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f358])).

fof(f1144,plain,
    ( spl7_55
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f368,f353,f1141])).

fof(f368,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f355,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1074,plain,
    ( spl7_51
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f1024,f649,f1071])).

fof(f649,plain,
    ( spl7_40
  <=> l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f1024,plain,
    ( l1_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f650,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f650,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f649])).

fof(f1056,plain,
    ( spl7_6
    | ~ spl7_20
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f1012,f582,f393,f158])).

fof(f393,plain,
    ( spl7_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f582,plain,
    ( spl7_33
  <=> u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f1012,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_20
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f394,f584])).

fof(f584,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f582])).

fof(f394,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f393])).

fof(f1010,plain,
    ( spl7_50
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f631,f353,f168,f1007])).

fof(f1007,plain,
    ( spl7_50
  <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f631,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f355,f170,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f170,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f661,plain,
    ( ~ spl7_37
    | ~ spl7_2
    | spl7_40 ),
    inference(avatar_split_clause,[],[f657,f649,f134,f623])).

fof(f657,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl7_2
    | spl7_40 ),
    inference(unit_resulting_resolution,[],[f136,f651,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f651,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK2,sK3))
    | spl7_40 ),
    inference(avatar_component_clause,[],[f649])).

fof(f656,plain,
    ( ~ spl7_40
    | spl7_41
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f621,f615,f653,f649])).

fof(f615,plain,
    ( spl7_36
  <=> v1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f621,plain,
    ( k1_pre_topc(sK2,sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3)))
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl7_36 ),
    inference(resolution,[],[f617,f78])).

fof(f617,plain,
    ( v1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f615])).

fof(f647,plain,
    ( ~ spl7_6
    | spl7_39
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f627,f615,f134,f644,f158])).

fof(f627,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f620,f136])).

fof(f620,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_36 ),
    inference(resolution,[],[f617,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f123,f117])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f626,plain,
    ( spl7_37
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f610,f158,f134,f623])).

fof(f610,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f160,f117])).

fof(f618,plain,
    ( spl7_36
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f609,f158,f134,f615])).

fof(f609,plain,
    ( v1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f136,f160,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f585,plain,
    ( spl7_33
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f340,f307,f223,f134,f582])).

fof(f223,plain,
    ( spl7_10
  <=> v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f307,plain,
    ( spl7_15
  <=> l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f340,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f330,f228])).

fof(f228,plain,
    ( u1_struct_0(sK2) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f136,f124,f225,f127])).

fof(f225,plain,
    ( v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f223])).

fof(f330,plain,
    ( k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f309,f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f75,f76])).

fof(f309,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f307])).

fof(f361,plain,
    ( spl7_17
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f258,f248,f358])).

fof(f248,plain,
    ( spl7_12
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f258,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f250,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f250,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f248])).

fof(f356,plain,
    ( spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f257,f248,f353])).

fof(f257,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f250,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f310,plain,
    ( spl7_15
    | ~ spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f238,f232,f134,f307])).

fof(f232,plain,
    ( spl7_11
  <=> m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f238,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_2
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f136,f234,f100])).

fof(f234,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f232])).

fof(f251,plain,
    ( spl7_12
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f176,f134,f248])).

fof(f176,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f136,f77])).

fof(f235,plain,
    ( spl7_11
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f190,f134,f232])).

fof(f190,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f136,f124,f117])).

fof(f226,plain,
    ( spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f188,f134,f223])).

fof(f188,plain,
    ( v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f136,f124,f116])).

fof(f185,plain,
    ( spl7_6
    | spl7_8 ),
    inference(avatar_split_clause,[],[f71,f168,f158])).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f154,plain,
    ( spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f68,f151,f147])).

fof(f68,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f137,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f67,f134])).

fof(f67,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (14145)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.46  % (14137)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (14135)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (14150)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (14142)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (14129)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14130)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (14129)Refutation not found, incomplete strategy% (14129)------------------------------
% 0.21/0.50  % (14129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14129)Memory used [KB]: 10746
% 0.21/0.50  % (14129)Time elapsed: 0.095 s
% 0.21/0.50  % (14129)------------------------------
% 0.21/0.50  % (14129)------------------------------
% 0.21/0.50  % (14128)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14144)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (14128)Refutation not found, incomplete strategy% (14128)------------------------------
% 0.21/0.50  % (14128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14128)Memory used [KB]: 10618
% 0.21/0.50  % (14128)Time elapsed: 0.094 s
% 0.21/0.50  % (14128)------------------------------
% 0.21/0.50  % (14128)------------------------------
% 0.21/0.51  % (14136)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (14138)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (14132)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (14146)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (14131)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (14149)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (14143)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (14133)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (14134)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (14134)Refutation not found, incomplete strategy% (14134)------------------------------
% 0.21/0.52  % (14134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14134)Memory used [KB]: 10618
% 0.21/0.52  % (14134)Time elapsed: 0.082 s
% 0.21/0.52  % (14134)------------------------------
% 0.21/0.52  % (14134)------------------------------
% 0.21/0.53  % (14140)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (14151)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (14139)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (14141)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (14152)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (14147)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (14148)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (14153)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (14133)Refutation not found, incomplete strategy% (14133)------------------------------
% 0.21/0.55  % (14133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14133)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14133)Memory used [KB]: 6524
% 0.21/0.55  % (14133)Time elapsed: 0.151 s
% 0.21/0.55  % (14133)------------------------------
% 0.21/0.55  % (14133)------------------------------
% 1.73/0.58  % (14137)Refutation not found, incomplete strategy% (14137)------------------------------
% 1.73/0.58  % (14137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (14137)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (14137)Memory used [KB]: 6140
% 1.73/0.60  % (14137)Time elapsed: 0.176 s
% 1.73/0.60  % (14137)------------------------------
% 1.73/0.60  % (14137)------------------------------
% 2.83/0.75  % (14151)Refutation found. Thanks to Tanya!
% 2.83/0.75  % SZS status Theorem for theBenchmark
% 2.83/0.75  % SZS output start Proof for theBenchmark
% 2.83/0.75  fof(f2928,plain,(
% 2.83/0.75    $false),
% 2.83/0.75    inference(avatar_sat_refutation,[],[f137,f154,f185,f226,f235,f251,f310,f356,f361,f585,f618,f626,f647,f656,f661,f1010,f1056,f1074,f1144,f1266,f1589,f1679,f1680,f1778,f2054,f2063,f2078,f2382,f2895,f2922,f2927])).
% 2.83/0.75  fof(f2927,plain,(
% 2.83/0.75    u1_struct_0(sK2) != u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))),
% 2.83/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.83/0.75  fof(f2922,plain,(
% 2.83/0.75    ~spl7_2 | ~spl7_6 | ~spl7_16 | ~spl7_37 | ~spl7_43 | ~spl7_77 | ~spl7_92 | ~spl7_95),
% 2.83/0.75    inference(avatar_contradiction_clause,[],[f2921])).
% 2.83/0.75  fof(f2921,plain,(
% 2.83/0.75    $false | (~spl7_2 | ~spl7_6 | ~spl7_16 | ~spl7_37 | ~spl7_43 | ~spl7_77 | ~spl7_92 | ~spl7_95)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2920,f124])).
% 2.83/0.75  fof(f124,plain,(
% 2.83/0.75    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.83/0.75    inference(forward_demodulation,[],[f74,f73])).
% 2.83/0.75  fof(f73,plain,(
% 2.83/0.75    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.83/0.75    inference(cnf_transformation,[],[f2])).
% 2.83/0.75  fof(f2,axiom,(
% 2.83/0.75    ! [X0] : k2_subset_1(X0) = X0),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.83/0.75  fof(f74,plain,(
% 2.83/0.75    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.83/0.75    inference(cnf_transformation,[],[f3])).
% 2.83/0.75  fof(f3,axiom,(
% 2.83/0.75    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.83/0.75  fof(f2920,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | (~spl7_2 | ~spl7_6 | ~spl7_16 | ~spl7_37 | ~spl7_43 | ~spl7_77 | ~spl7_92 | ~spl7_95)),
% 2.83/0.75    inference(forward_demodulation,[],[f2919,f2067])).
% 2.83/0.75  fof(f2067,plain,(
% 2.83/0.75    sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl7_95),
% 2.83/0.75    inference(avatar_component_clause,[],[f2065])).
% 2.83/0.75  fof(f2065,plain,(
% 2.83/0.75    spl7_95 <=> sK3 = u1_struct_0(k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 2.83/0.75  fof(f2919,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | (~spl7_2 | ~spl7_6 | ~spl7_16 | ~spl7_37 | ~spl7_43 | ~spl7_77 | ~spl7_92 | ~spl7_95)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2904,f2918])).
% 2.83/0.75  fof(f2918,plain,(
% 2.83/0.75    ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl7_2 | ~spl7_6 | ~spl7_37 | ~spl7_77 | ~spl7_92 | ~spl7_95)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2897,f2917])).
% 2.83/0.75  fof(f2917,plain,(
% 2.83/0.75    v2_compts_1(sK3,sK2) | (~spl7_2 | ~spl7_37 | ~spl7_77 | ~spl7_95)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2916,f124])).
% 2.83/0.75  fof(f2916,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | v2_compts_1(sK3,sK2) | (~spl7_2 | ~spl7_37 | ~spl7_77 | ~spl7_95)),
% 2.83/0.75    inference(forward_demodulation,[],[f2905,f2067])).
% 2.83/0.75  fof(f2905,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(sK3,sK2) | (~spl7_2 | ~spl7_37 | ~spl7_77)),
% 2.83/0.75    inference(resolution,[],[f1773,f1627])).
% 2.83/0.75  fof(f1627,plain,(
% 2.83/0.75    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X1,sK2)) ) | (~spl7_2 | ~spl7_37)),
% 2.83/0.75    inference(subsumption_resolution,[],[f1623,f136])).
% 2.83/0.75  fof(f136,plain,(
% 2.83/0.75    l1_pre_topc(sK2) | ~spl7_2),
% 2.83/0.75    inference(avatar_component_clause,[],[f134])).
% 2.83/0.75  fof(f134,plain,(
% 2.83/0.75    spl7_2 <=> l1_pre_topc(sK2)),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.83/0.75  fof(f1623,plain,(
% 2.83/0.75    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X1,sK2) | ~l1_pre_topc(sK2)) ) | ~spl7_37),
% 2.83/0.75    inference(resolution,[],[f625,f125])).
% 2.83/0.75  fof(f125,plain,(
% 2.83/0.75    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X3,X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(subsumption_resolution,[],[f119,f101])).
% 2.83/0.75  fof(f101,plain,(
% 2.83/0.75    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f33])).
% 2.83/0.75  fof(f33,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f15])).
% 2.83/0.75  fof(f15,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 2.83/0.75  fof(f119,plain,(
% 2.83/0.75    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(equality_resolution,[],[f103])).
% 2.83/0.75  fof(f103,plain,(
% 2.83/0.75    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f63])).
% 2.83/0.75  fof(f63,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(nnf_transformation,[],[f35])).
% 2.83/0.75  fof(f35,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f34])).
% 2.83/0.75  fof(f34,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f18])).
% 2.83/0.75  fof(f18,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).
% 2.83/0.75  fof(f625,plain,(
% 2.83/0.75    m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | ~spl7_37),
% 2.83/0.75    inference(avatar_component_clause,[],[f623])).
% 2.83/0.75  fof(f623,plain,(
% 2.83/0.75    spl7_37 <=> m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 2.83/0.75  fof(f1773,plain,(
% 2.83/0.75    v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) | ~spl7_77),
% 2.83/0.75    inference(avatar_component_clause,[],[f1771])).
% 2.83/0.75  fof(f1771,plain,(
% 2.83/0.75    spl7_77 <=> v2_compts_1(sK3,k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 2.83/0.75  fof(f2897,plain,(
% 2.83/0.75    ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_compts_1(sK3,sK2) | (~spl7_6 | ~spl7_92)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2896,f160])).
% 2.83/0.75  fof(f160,plain,(
% 2.83/0.75    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_6),
% 2.83/0.75    inference(avatar_component_clause,[],[f158])).
% 2.83/0.75  fof(f158,plain,(
% 2.83/0.75    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.83/0.75  fof(f2896,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_compts_1(sK3,sK2) | (~spl7_6 | ~spl7_92)),
% 2.83/0.75    inference(forward_demodulation,[],[f1591,f2053])).
% 2.83/0.75  fof(f2053,plain,(
% 2.83/0.75    u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_92),
% 2.83/0.75    inference(avatar_component_clause,[],[f2051])).
% 2.83/0.75  fof(f2051,plain,(
% 2.83/0.75    spl7_92 <=> u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 2.83/0.75  fof(f1591,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_compts_1(sK3,sK2) | ~spl7_6),
% 2.83/0.75    inference(subsumption_resolution,[],[f72,f160])).
% 2.83/0.75  fof(f72,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_compts_1(sK3,sK2)),
% 2.83/0.75    inference(cnf_transformation,[],[f54])).
% 2.83/0.75  fof(f54,plain,(
% 2.83/0.75    ((~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_compts_1(sK3,sK2)) & ((m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v2_compts_1(sK3,sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 2.83/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).
% 2.83/0.75  fof(f52,plain,(
% 2.83/0.75    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_compts_1(X1,sK2)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v2_compts_1(X1,sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 2.83/0.75    introduced(choice_axiom,[])).
% 2.83/0.75  fof(f53,plain,(
% 2.83/0.75    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_compts_1(X1,sK2)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v2_compts_1(X1,sK2)))) => ((~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_compts_1(sK3,sK2)) & ((m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v2_compts_1(sK3,sK2))))),
% 2.83/0.75    introduced(choice_axiom,[])).
% 2.83/0.75  fof(f51,plain,(
% 2.83/0.75    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f50])).
% 2.83/0.75  fof(f50,plain,(
% 2.83/0.75    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.83/0.75    inference(nnf_transformation,[],[f24])).
% 2.83/0.75  fof(f24,plain,(
% 2.83/0.75    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f23])).
% 2.83/0.75  fof(f23,plain,(
% 2.83/0.75    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.83/0.75    inference(ennf_transformation,[],[f22])).
% 2.83/0.75  fof(f22,plain,(
% 2.83/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.83/0.75    inference(pure_predicate_removal,[],[f20])).
% 2.83/0.75  fof(f20,negated_conjecture,(
% 2.83/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.83/0.75    inference(negated_conjecture,[],[f19])).
% 2.83/0.75  fof(f19,conjecture,(
% 2.83/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).
% 2.83/0.75  fof(f2904,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl7_16 | ~spl7_43 | ~spl7_77)),
% 2.83/0.75    inference(resolution,[],[f1773,f1740])).
% 2.83/0.75  fof(f1740,plain,(
% 2.83/0.75    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ) | (~spl7_16 | ~spl7_43)),
% 2.83/0.75    inference(subsumption_resolution,[],[f1735,f355])).
% 2.83/0.75  fof(f355,plain,(
% 2.83/0.75    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_16),
% 2.83/0.75    inference(avatar_component_clause,[],[f353])).
% 2.83/0.75  fof(f353,plain,(
% 2.83/0.75    spl7_16 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.83/0.75  fof(f1735,plain,(
% 2.83/0.75    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ) | ~spl7_43),
% 2.83/0.75    inference(resolution,[],[f724,f125])).
% 2.83/0.75  fof(f724,plain,(
% 2.83/0.75    m1_pre_topc(k1_pre_topc(sK2,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_43),
% 2.83/0.75    inference(avatar_component_clause,[],[f723])).
% 2.83/0.75  fof(f723,plain,(
% 2.83/0.75    spl7_43 <=> m1_pre_topc(k1_pre_topc(sK2,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.83/0.75  fof(f2895,plain,(
% 2.83/0.75    spl7_77 | ~spl7_5 | ~spl7_16 | ~spl7_43 | ~spl7_95),
% 2.83/0.75    inference(avatar_split_clause,[],[f2835,f2065,f723,f353,f151,f1771])).
% 2.83/0.75  fof(f151,plain,(
% 2.83/0.75    spl7_5 <=> v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.83/0.75  fof(f2835,plain,(
% 2.83/0.75    v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) | (~spl7_5 | ~spl7_16 | ~spl7_43 | ~spl7_95)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2834,f124])).
% 2.83/0.75  fof(f2834,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) | (~spl7_5 | ~spl7_16 | ~spl7_43 | ~spl7_95)),
% 2.83/0.75    inference(forward_demodulation,[],[f2833,f2067])).
% 2.83/0.75  fof(f2833,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) | (~spl7_5 | ~spl7_16 | ~spl7_43)),
% 2.83/0.75    inference(resolution,[],[f1739,f153])).
% 2.83/0.75  fof(f153,plain,(
% 2.83/0.75    v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_5),
% 2.83/0.75    inference(avatar_component_clause,[],[f151])).
% 2.83/0.75  fof(f1739,plain,(
% 2.83/0.75    ( ! [X0] : (~v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X0,k1_pre_topc(sK2,sK3))) ) | (~spl7_16 | ~spl7_43)),
% 2.83/0.75    inference(subsumption_resolution,[],[f1734,f355])).
% 2.83/0.75  fof(f1734,plain,(
% 2.83/0.75    ( ! [X0] : (~v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ) | ~spl7_43),
% 2.83/0.75    inference(resolution,[],[f724,f126])).
% 2.83/0.75  fof(f126,plain,(
% 2.83/0.75    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X3,X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(subsumption_resolution,[],[f120,f101])).
% 2.83/0.75  fof(f120,plain,(
% 2.83/0.75    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(equality_resolution,[],[f102])).
% 2.83/0.75  fof(f102,plain,(
% 2.83/0.75    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f63])).
% 2.83/0.75  fof(f2382,plain,(
% 2.83/0.75    spl7_78 | ~spl7_95),
% 2.83/0.75    inference(avatar_contradiction_clause,[],[f2381])).
% 2.83/0.75  fof(f2381,plain,(
% 2.83/0.75    $false | (spl7_78 | ~spl7_95)),
% 2.83/0.75    inference(subsumption_resolution,[],[f2347,f124])).
% 2.83/0.75  fof(f2347,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | (spl7_78 | ~spl7_95)),
% 2.83/0.75    inference(superposition,[],[f1777,f2067])).
% 2.83/0.75  fof(f1777,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | spl7_78),
% 2.83/0.75    inference(avatar_component_clause,[],[f1775])).
% 2.83/0.75  fof(f1775,plain,(
% 2.83/0.75    spl7_78 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3))))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 2.83/0.75  fof(f2078,plain,(
% 2.83/0.75    spl7_95 | ~spl7_39 | ~spl7_94),
% 2.83/0.75    inference(avatar_split_clause,[],[f2072,f2060,f644,f2065])).
% 2.83/0.75  fof(f644,plain,(
% 2.83/0.75    spl7_39 <=> sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 2.83/0.75  fof(f2060,plain,(
% 2.83/0.75    spl7_94 <=> u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).
% 2.83/0.75  fof(f2072,plain,(
% 2.83/0.75    sK3 = u1_struct_0(k1_pre_topc(sK2,sK3)) | (~spl7_39 | ~spl7_94)),
% 2.83/0.75    inference(forward_demodulation,[],[f2062,f646])).
% 2.83/0.75  fof(f646,plain,(
% 2.83/0.75    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~spl7_39),
% 2.83/0.75    inference(avatar_component_clause,[],[f644])).
% 2.83/0.75  fof(f2062,plain,(
% 2.83/0.75    u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~spl7_94),
% 2.83/0.75    inference(avatar_component_clause,[],[f2060])).
% 2.83/0.75  fof(f2063,plain,(
% 2.83/0.75    spl7_94 | ~spl7_51),
% 2.83/0.75    inference(avatar_split_clause,[],[f1316,f1071,f2060])).
% 2.83/0.75  fof(f1071,plain,(
% 2.83/0.75    spl7_51 <=> l1_struct_0(k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.83/0.75  fof(f1316,plain,(
% 2.83/0.75    u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~spl7_51),
% 2.83/0.75    inference(resolution,[],[f1073,f75])).
% 2.83/0.75  fof(f75,plain,(
% 2.83/0.75    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f25])).
% 2.83/0.75  fof(f25,plain,(
% 2.83/0.75    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f8])).
% 2.83/0.75  fof(f8,axiom,(
% 2.83/0.75    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.83/0.75  fof(f1073,plain,(
% 2.83/0.75    l1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl7_51),
% 2.83/0.75    inference(avatar_component_clause,[],[f1071])).
% 2.83/0.75  fof(f2054,plain,(
% 2.83/0.75    spl7_92 | ~spl7_55 | ~spl7_60),
% 2.83/0.75    inference(avatar_split_clause,[],[f1270,f1263,f1141,f2051])).
% 2.83/0.75  fof(f1141,plain,(
% 2.83/0.75    spl7_55 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 2.83/0.75  fof(f1263,plain,(
% 2.83/0.75    spl7_60 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 2.83/0.75  fof(f1270,plain,(
% 2.83/0.75    u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl7_55 | ~spl7_60)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f1143,f1265,f114])).
% 2.83/0.75  fof(f114,plain,(
% 2.83/0.75    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.83/0.75    inference(cnf_transformation,[],[f43])).
% 2.83/0.75  fof(f43,plain,(
% 2.83/0.75    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.83/0.75    inference(ennf_transformation,[],[f14])).
% 2.83/0.75  fof(f14,axiom,(
% 2.83/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 2.83/0.75  fof(f1265,plain,(
% 2.83/0.75    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~spl7_60),
% 2.83/0.75    inference(avatar_component_clause,[],[f1263])).
% 2.83/0.75  fof(f1143,plain,(
% 2.83/0.75    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~spl7_55),
% 2.83/0.75    inference(avatar_component_clause,[],[f1141])).
% 2.83/0.75  fof(f1778,plain,(
% 2.83/0.75    spl7_77 | ~spl7_78 | ~spl7_2 | ~spl7_4 | ~spl7_37),
% 2.83/0.75    inference(avatar_split_clause,[],[f1703,f623,f147,f134,f1775,f1771])).
% 2.83/0.75  fof(f147,plain,(
% 2.83/0.75    spl7_4 <=> v2_compts_1(sK3,sK2)),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.83/0.75  fof(f1703,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) | (~spl7_2 | ~spl7_4 | ~spl7_37)),
% 2.83/0.75    inference(resolution,[],[f1626,f149])).
% 2.83/0.75  fof(f149,plain,(
% 2.83/0.75    v2_compts_1(sK3,sK2) | ~spl7_4),
% 2.83/0.75    inference(avatar_component_clause,[],[f147])).
% 2.83/0.75  fof(f1626,plain,(
% 2.83/0.75    ( ! [X0] : (~v2_compts_1(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X0,k1_pre_topc(sK2,sK3))) ) | (~spl7_2 | ~spl7_37)),
% 2.83/0.75    inference(subsumption_resolution,[],[f1622,f136])).
% 2.83/0.75  fof(f1622,plain,(
% 2.83/0.75    ( ! [X0] : (~v2_compts_1(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK3)))) | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2)) ) | ~spl7_37),
% 2.83/0.75    inference(resolution,[],[f625,f126])).
% 2.83/0.75  fof(f1680,plain,(
% 2.83/0.75    k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != k1_pre_topc(sK2,sK3) | m1_pre_topc(k1_pre_topc(sK2,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.83/0.75  fof(f1679,plain,(
% 2.83/0.75    spl7_71 | ~spl7_2 | ~spl7_6 | ~spl7_41 | ~spl7_55 | ~spl7_60),
% 2.83/0.75    inference(avatar_split_clause,[],[f1614,f1263,f1141,f653,f158,f134,f1676])).
% 2.83/0.75  fof(f1676,plain,(
% 2.83/0.75    spl7_71 <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = k1_pre_topc(sK2,sK3)),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 2.83/0.75  fof(f653,plain,(
% 2.83/0.75    spl7_41 <=> k1_pre_topc(sK2,sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 2.83/0.75  fof(f1614,plain,(
% 2.83/0.75    k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = k1_pre_topc(sK2,sK3) | (~spl7_2 | ~spl7_6 | ~spl7_41 | ~spl7_55 | ~spl7_60)),
% 2.83/0.75    inference(forward_demodulation,[],[f1613,f655])).
% 2.83/0.75  fof(f655,plain,(
% 2.83/0.75    k1_pre_topc(sK2,sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3))) | ~spl7_41),
% 2.83/0.75    inference(avatar_component_clause,[],[f653])).
% 2.83/0.75  fof(f1613,plain,(
% 2.83/0.75    k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3))) | (~spl7_2 | ~spl7_6 | ~spl7_55 | ~spl7_60)),
% 2.83/0.75    inference(subsumption_resolution,[],[f1612,f160])).
% 2.83/0.75  fof(f1612,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3))) | (~spl7_2 | ~spl7_6 | ~spl7_55 | ~spl7_60)),
% 2.83/0.75    inference(forward_demodulation,[],[f1607,f1270])).
% 2.83/0.75  fof(f1607,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3))) | (~spl7_2 | ~spl7_6)),
% 2.83/0.75    inference(resolution,[],[f160,f227])).
% 2.83/0.75  fof(f227,plain,(
% 2.83/0.75    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,X0)),u1_pre_topc(k1_pre_topc(sK2,X0)))) ) | ~spl7_2),
% 2.83/0.75    inference(resolution,[],[f121,f136])).
% 2.83/0.75  fof(f121,plain,(
% 2.83/0.75    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2)))) )),
% 2.83/0.75    inference(equality_resolution,[],[f104])).
% 2.83/0.75  fof(f104,plain,(
% 2.83/0.75    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f37])).
% 2.83/0.75  fof(f37,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f36])).
% 2.83/0.75  fof(f36,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f17])).
% 2.83/0.75  fof(f17,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).
% 2.83/0.75  fof(f1589,plain,(
% 2.83/0.75    ~spl7_6 | spl7_8 | ~spl7_55 | ~spl7_60),
% 2.83/0.75    inference(avatar_contradiction_clause,[],[f1588])).
% 2.83/0.75  fof(f1588,plain,(
% 2.83/0.75    $false | (~spl7_6 | spl7_8 | ~spl7_55 | ~spl7_60)),
% 2.83/0.75    inference(subsumption_resolution,[],[f1585,f160])).
% 2.83/0.75  fof(f1585,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | (spl7_8 | ~spl7_55 | ~spl7_60)),
% 2.83/0.75    inference(forward_demodulation,[],[f169,f1270])).
% 2.83/0.75  fof(f169,plain,(
% 2.83/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | spl7_8),
% 2.83/0.75    inference(avatar_component_clause,[],[f168])).
% 2.83/0.75  fof(f168,plain,(
% 2.83/0.75    spl7_8 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.83/0.75  fof(f1266,plain,(
% 2.83/0.75    spl7_60 | ~spl7_16 | ~spl7_17),
% 2.83/0.75    inference(avatar_split_clause,[],[f382,f358,f353,f1263])).
% 2.83/0.75  fof(f358,plain,(
% 2.83/0.75    spl7_17 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.83/0.75  fof(f382,plain,(
% 2.83/0.75    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (~spl7_16 | ~spl7_17)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f355,f360,f78])).
% 2.83/0.75  fof(f78,plain,(
% 2.83/0.75    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f29])).
% 2.83/0.75  fof(f29,plain,(
% 2.83/0.75    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f28])).
% 2.83/0.75  fof(f28,plain,(
% 2.83/0.75    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f5])).
% 2.83/0.75  fof(f5,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 2.83/0.75  fof(f360,plain,(
% 2.83/0.75    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_17),
% 2.83/0.75    inference(avatar_component_clause,[],[f358])).
% 2.83/0.75  fof(f1144,plain,(
% 2.83/0.75    spl7_55 | ~spl7_16),
% 2.83/0.75    inference(avatar_split_clause,[],[f368,f353,f1141])).
% 2.83/0.75  fof(f368,plain,(
% 2.83/0.75    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~spl7_16),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f355,f77])).
% 2.83/0.75  fof(f77,plain,(
% 2.83/0.75    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f27])).
% 2.83/0.75  fof(f27,plain,(
% 2.83/0.75    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f13])).
% 2.83/0.75  fof(f13,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.83/0.75  fof(f1074,plain,(
% 2.83/0.75    spl7_51 | ~spl7_40),
% 2.83/0.75    inference(avatar_split_clause,[],[f1024,f649,f1071])).
% 2.83/0.75  fof(f649,plain,(
% 2.83/0.75    spl7_40 <=> l1_pre_topc(k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 2.83/0.75  fof(f1024,plain,(
% 2.83/0.75    l1_struct_0(k1_pre_topc(sK2,sK3)) | ~spl7_40),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f650,f76])).
% 2.83/0.75  fof(f76,plain,(
% 2.83/0.75    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f26])).
% 2.83/0.75  fof(f26,plain,(
% 2.83/0.75    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f11])).
% 2.83/0.75  fof(f11,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.83/0.75  fof(f650,plain,(
% 2.83/0.75    l1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl7_40),
% 2.83/0.75    inference(avatar_component_clause,[],[f649])).
% 2.83/0.75  fof(f1056,plain,(
% 2.83/0.75    spl7_6 | ~spl7_20 | ~spl7_33),
% 2.83/0.75    inference(avatar_split_clause,[],[f1012,f582,f393,f158])).
% 2.83/0.75  fof(f393,plain,(
% 2.83/0.75    spl7_20 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 2.83/0.75  fof(f582,plain,(
% 2.83/0.75    spl7_33 <=> u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 2.83/0.75  fof(f1012,plain,(
% 2.83/0.75    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl7_20 | ~spl7_33)),
% 2.83/0.75    inference(forward_demodulation,[],[f394,f584])).
% 2.83/0.75  fof(f584,plain,(
% 2.83/0.75    u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) | ~spl7_33),
% 2.83/0.75    inference(avatar_component_clause,[],[f582])).
% 2.83/0.75  fof(f394,plain,(
% 2.83/0.75    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))))) | ~spl7_20),
% 2.83/0.75    inference(avatar_component_clause,[],[f393])).
% 2.83/0.75  fof(f1010,plain,(
% 2.83/0.75    spl7_50 | ~spl7_8 | ~spl7_16),
% 2.83/0.75    inference(avatar_split_clause,[],[f631,f353,f168,f1007])).
% 2.83/0.75  fof(f1007,plain,(
% 2.83/0.75    spl7_50 <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.83/0.75  fof(f631,plain,(
% 2.83/0.75    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl7_8 | ~spl7_16)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f355,f170,f117])).
% 2.83/0.75  fof(f117,plain,(
% 2.83/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f45])).
% 2.83/0.75  fof(f45,plain,(
% 2.83/0.75    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f44])).
% 2.83/0.75  fof(f44,plain,(
% 2.83/0.75    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.83/0.75    inference(ennf_transformation,[],[f10])).
% 2.83/0.75  fof(f10,axiom,(
% 2.83/0.75    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 2.83/0.75  fof(f170,plain,(
% 2.83/0.75    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~spl7_8),
% 2.83/0.75    inference(avatar_component_clause,[],[f168])).
% 2.83/0.75  fof(f661,plain,(
% 2.83/0.75    ~spl7_37 | ~spl7_2 | spl7_40),
% 2.83/0.75    inference(avatar_split_clause,[],[f657,f649,f134,f623])).
% 2.83/0.75  fof(f657,plain,(
% 2.83/0.75    ~m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | (~spl7_2 | spl7_40)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f136,f651,f100])).
% 2.83/0.75  fof(f100,plain,(
% 2.83/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f32])).
% 2.83/0.75  fof(f32,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f12])).
% 2.83/0.75  fof(f12,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.83/0.75  fof(f651,plain,(
% 2.83/0.75    ~l1_pre_topc(k1_pre_topc(sK2,sK3)) | spl7_40),
% 2.83/0.75    inference(avatar_component_clause,[],[f649])).
% 2.83/0.75  fof(f656,plain,(
% 2.83/0.75    ~spl7_40 | spl7_41 | ~spl7_36),
% 2.83/0.75    inference(avatar_split_clause,[],[f621,f615,f653,f649])).
% 2.83/0.75  fof(f615,plain,(
% 2.83/0.75    spl7_36 <=> v1_pre_topc(k1_pre_topc(sK2,sK3))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.83/0.75  fof(f621,plain,(
% 2.83/0.75    k1_pre_topc(sK2,sK3) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK2,sK3)),u1_pre_topc(k1_pre_topc(sK2,sK3))) | ~l1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl7_36),
% 2.83/0.75    inference(resolution,[],[f617,f78])).
% 2.83/0.75  fof(f617,plain,(
% 2.83/0.75    v1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl7_36),
% 2.83/0.75    inference(avatar_component_clause,[],[f615])).
% 2.83/0.75  fof(f647,plain,(
% 2.83/0.75    ~spl7_6 | spl7_39 | ~spl7_2 | ~spl7_36),
% 2.83/0.75    inference(avatar_split_clause,[],[f627,f615,f134,f644,f158])).
% 2.83/0.75  fof(f627,plain,(
% 2.83/0.75    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl7_2 | ~spl7_36)),
% 2.83/0.75    inference(subsumption_resolution,[],[f620,f136])).
% 2.83/0.75  fof(f620,plain,(
% 2.83/0.75    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~spl7_36),
% 2.83/0.75    inference(resolution,[],[f617,f127])).
% 2.83/0.75  fof(f127,plain,(
% 2.83/0.75    ( ! [X0,X1] : (~v1_pre_topc(k1_pre_topc(X0,X1)) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(subsumption_resolution,[],[f123,f117])).
% 2.83/0.75  fof(f123,plain,(
% 2.83/0.75    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(equality_resolution,[],[f105])).
% 2.83/0.75  fof(f105,plain,(
% 2.83/0.75    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.75    inference(cnf_transformation,[],[f64])).
% 2.83/0.75  fof(f64,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(nnf_transformation,[],[f39])).
% 2.83/0.75  fof(f39,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(flattening,[],[f38])).
% 2.83/0.75  fof(f38,plain,(
% 2.83/0.75    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.75    inference(ennf_transformation,[],[f6])).
% 2.83/0.75  fof(f6,axiom,(
% 2.83/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 2.83/0.75  fof(f626,plain,(
% 2.83/0.75    spl7_37 | ~spl7_2 | ~spl7_6),
% 2.83/0.75    inference(avatar_split_clause,[],[f610,f158,f134,f623])).
% 2.83/0.75  fof(f610,plain,(
% 2.83/0.75    m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | (~spl7_2 | ~spl7_6)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f136,f160,f117])).
% 2.83/0.75  fof(f618,plain,(
% 2.83/0.75    spl7_36 | ~spl7_2 | ~spl7_6),
% 2.83/0.75    inference(avatar_split_clause,[],[f609,f158,f134,f615])).
% 2.83/0.75  fof(f609,plain,(
% 2.83/0.75    v1_pre_topc(k1_pre_topc(sK2,sK3)) | (~spl7_2 | ~spl7_6)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f136,f160,f116])).
% 2.83/0.75  fof(f116,plain,(
% 2.83/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 2.83/0.75    inference(cnf_transformation,[],[f45])).
% 2.83/0.75  fof(f585,plain,(
% 2.83/0.75    spl7_33 | ~spl7_2 | ~spl7_10 | ~spl7_15),
% 2.83/0.75    inference(avatar_split_clause,[],[f340,f307,f223,f134,f582])).
% 2.83/0.75  fof(f223,plain,(
% 2.83/0.75    spl7_10 <=> v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.83/0.75  fof(f307,plain,(
% 2.83/0.75    spl7_15 <=> l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.83/0.75  fof(f340,plain,(
% 2.83/0.75    u1_struct_0(sK2) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) | (~spl7_2 | ~spl7_10 | ~spl7_15)),
% 2.83/0.75    inference(forward_demodulation,[],[f330,f228])).
% 2.83/0.75  fof(f228,plain,(
% 2.83/0.75    u1_struct_0(sK2) = k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) | (~spl7_2 | ~spl7_10)),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f136,f124,f225,f127])).
% 2.83/0.75  fof(f225,plain,(
% 2.83/0.75    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) | ~spl7_10),
% 2.83/0.75    inference(avatar_component_clause,[],[f223])).
% 2.83/0.75  fof(f330,plain,(
% 2.83/0.75    k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) = u1_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) | ~spl7_15),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f309,f156])).
% 2.83/0.75  fof(f156,plain,(
% 2.83/0.75    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.83/0.75    inference(resolution,[],[f75,f76])).
% 2.83/0.75  fof(f309,plain,(
% 2.83/0.75    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) | ~spl7_15),
% 2.83/0.75    inference(avatar_component_clause,[],[f307])).
% 2.83/0.75  fof(f361,plain,(
% 2.83/0.75    spl7_17 | ~spl7_12),
% 2.83/0.75    inference(avatar_split_clause,[],[f258,f248,f358])).
% 2.83/0.75  fof(f248,plain,(
% 2.83/0.75    spl7_12 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 2.83/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.83/0.75  fof(f258,plain,(
% 2.83/0.75    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_12),
% 2.83/0.75    inference(unit_resulting_resolution,[],[f250,f112])).
% 2.83/0.75  fof(f112,plain,(
% 2.83/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 2.83/0.75    inference(cnf_transformation,[],[f42])).
% 2.83/0.75  fof(f42,plain,(
% 2.83/0.75    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.83/0.75    inference(ennf_transformation,[],[f9])).
% 2.83/0.75  fof(f9,axiom,(
% 2.83/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.83/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.20/0.77  fof(f250,plain,(
% 3.20/0.77    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl7_12),
% 3.20/0.77    inference(avatar_component_clause,[],[f248])).
% 3.20/0.77  fof(f356,plain,(
% 3.20/0.77    spl7_16 | ~spl7_12),
% 3.20/0.77    inference(avatar_split_clause,[],[f257,f248,f353])).
% 3.20/0.77  fof(f257,plain,(
% 3.20/0.77    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl7_12),
% 3.20/0.77    inference(unit_resulting_resolution,[],[f250,f113])).
% 3.20/0.77  fof(f113,plain,(
% 3.20/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 3.20/0.77    inference(cnf_transformation,[],[f42])).
% 3.20/0.77  fof(f310,plain,(
% 3.20/0.77    spl7_15 | ~spl7_2 | ~spl7_11),
% 3.20/0.77    inference(avatar_split_clause,[],[f238,f232,f134,f307])).
% 3.20/0.77  fof(f232,plain,(
% 3.20/0.77    spl7_11 <=> m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2)),
% 3.20/0.77    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 3.20/0.77  fof(f238,plain,(
% 3.20/0.77    l1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) | (~spl7_2 | ~spl7_11)),
% 3.20/0.77    inference(unit_resulting_resolution,[],[f136,f234,f100])).
% 3.20/0.77  fof(f234,plain,(
% 3.20/0.77    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2) | ~spl7_11),
% 3.20/0.77    inference(avatar_component_clause,[],[f232])).
% 3.20/0.77  fof(f251,plain,(
% 3.20/0.77    spl7_12 | ~spl7_2),
% 3.20/0.77    inference(avatar_split_clause,[],[f176,f134,f248])).
% 3.20/0.77  fof(f176,plain,(
% 3.20/0.77    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl7_2),
% 3.20/0.77    inference(unit_resulting_resolution,[],[f136,f77])).
% 3.20/0.77  fof(f235,plain,(
% 3.20/0.77    spl7_11 | ~spl7_2),
% 3.20/0.77    inference(avatar_split_clause,[],[f190,f134,f232])).
% 3.20/0.77  fof(f190,plain,(
% 3.20/0.77    m1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2)),sK2) | ~spl7_2),
% 3.20/0.77    inference(unit_resulting_resolution,[],[f136,f124,f117])).
% 3.20/0.77  fof(f226,plain,(
% 3.20/0.77    spl7_10 | ~spl7_2),
% 3.20/0.77    inference(avatar_split_clause,[],[f188,f134,f223])).
% 3.20/0.77  fof(f188,plain,(
% 3.20/0.77    v1_pre_topc(k1_pre_topc(sK2,u1_struct_0(sK2))) | ~spl7_2),
% 3.20/0.77    inference(unit_resulting_resolution,[],[f136,f124,f116])).
% 3.20/0.77  fof(f185,plain,(
% 3.20/0.77    spl7_6 | spl7_8),
% 3.20/0.77    inference(avatar_split_clause,[],[f71,f168,f158])).
% 3.20/0.77  fof(f71,plain,(
% 3.20/0.77    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.20/0.77    inference(cnf_transformation,[],[f54])).
% 3.20/0.77  fof(f154,plain,(
% 3.20/0.77    spl7_4 | spl7_5),
% 3.20/0.77    inference(avatar_split_clause,[],[f68,f151,f147])).
% 3.20/0.77  fof(f68,plain,(
% 3.20/0.77    v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v2_compts_1(sK3,sK2)),
% 3.20/0.77    inference(cnf_transformation,[],[f54])).
% 3.20/0.77  fof(f137,plain,(
% 3.20/0.77    spl7_2),
% 3.20/0.77    inference(avatar_split_clause,[],[f67,f134])).
% 3.20/0.77  fof(f67,plain,(
% 3.20/0.77    l1_pre_topc(sK2)),
% 3.20/0.77    inference(cnf_transformation,[],[f54])).
% 3.20/0.77  % SZS output end Proof for theBenchmark
% 3.20/0.77  % (14151)------------------------------
% 3.20/0.77  % (14151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.77  % (14151)Termination reason: Refutation
% 3.20/0.77  
% 3.20/0.77  % (14151)Memory used [KB]: 12409
% 3.20/0.77  % (14151)Time elapsed: 0.358 s
% 3.20/0.77  % (14151)------------------------------
% 3.20/0.77  % (14151)------------------------------
% 3.20/0.78  % (14127)Success in time 0.411 s
%------------------------------------------------------------------------------
