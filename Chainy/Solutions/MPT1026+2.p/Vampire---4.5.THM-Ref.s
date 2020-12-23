%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1026+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 184 expanded)
%              Number of leaves         :   22 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  406 (1048 expanded)
%              Number of equality atoms :   65 ( 276 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2621,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1827,f1831,f1963,f1970,f1976,f2002,f2028,f2104,f2111,f2306,f2491,f2620])).

fof(f2620,plain,
    ( spl17_3
    | ~ spl17_37
    | ~ spl17_54 ),
    inference(avatar_contradiction_clause,[],[f2619])).

fof(f2619,plain,
    ( $false
    | spl17_3
    | ~ spl17_37
    | ~ spl17_54 ),
    inference(subsumption_resolution,[],[f2616,f2103])).

fof(f2103,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl17_37 ),
    inference(avatar_component_clause,[],[f2102])).

fof(f2102,plain,
    ( spl17_37
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_37])])).

fof(f2616,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl17_3
    | ~ spl17_54 ),
    inference(resolution,[],[f2597,f2305])).

fof(f2305,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))
    | ~ spl17_54 ),
    inference(avatar_component_clause,[],[f2304])).

fof(f2304,plain,
    ( spl17_54
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_54])])).

fof(f2597,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X3))
        | ~ r1_tarski(X3,sK1) )
    | spl17_3 ),
    inference(resolution,[],[f2562,f1726])).

fof(f1726,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1606])).

fof(f1606,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f334])).

fof(f334,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f2562,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(sK2,X2) )
    | spl17_3 ),
    inference(resolution,[],[f2558,f1694])).

fof(f1694,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1652])).

fof(f1652,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2558,plain,
    ( ! [X22] :
        ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_tarski(sK2,X22) )
    | spl17_3 ),
    inference(resolution,[],[f1721,f1826])).

fof(f1826,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl17_3 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f1825,plain,
    ( spl17_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f1721,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f1603])).

fof(f1603,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f1602])).

fof(f1602,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f1263])).

fof(f1263,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f2491,plain,
    ( ~ spl17_1
    | spl17_2
    | ~ spl17_15
    | ~ spl17_37
    | ~ spl17_38 ),
    inference(avatar_contradiction_clause,[],[f2490])).

fof(f2490,plain,
    ( $false
    | ~ spl17_1
    | spl17_2
    | ~ spl17_15
    | ~ spl17_37
    | ~ spl17_38 ),
    inference(subsumption_resolution,[],[f2488,f2103])).

fof(f2488,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl17_1
    | spl17_2
    | ~ spl17_15
    | ~ spl17_38 ),
    inference(resolution,[],[f2484,f1823])).

fof(f1823,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl17_2 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1822,plain,
    ( spl17_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f2484,plain,
    ( ! [X3] :
        ( v1_funct_2(sK2,sK0,X3)
        | ~ r1_tarski(k2_relat_1(sK2),X3) )
    | ~ spl17_1
    | ~ spl17_15
    | ~ spl17_38 ),
    inference(forward_demodulation,[],[f2483,f2110])).

fof(f2110,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl17_38 ),
    inference(avatar_component_clause,[],[f2109])).

fof(f2109,plain,
    ( spl17_38
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_38])])).

fof(f2483,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X3)
        | v1_funct_2(sK2,k1_relat_1(sK2),X3) )
    | ~ spl17_1
    | ~ spl17_15 ),
    inference(subsumption_resolution,[],[f2479,f1969])).

fof(f1969,plain,
    ( v1_relat_1(sK2)
    | ~ spl17_15 ),
    inference(avatar_component_clause,[],[f1968])).

fof(f1968,plain,
    ( spl17_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f2479,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X3)
        | v1_funct_2(sK2,k1_relat_1(sK2),X3)
        | ~ v1_relat_1(sK2) )
    | ~ spl17_1 ),
    inference(resolution,[],[f1759,f1975])).

fof(f1975,plain,
    ( v1_funct_1(sK2)
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f1819])).

fof(f1819,plain,
    ( spl17_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f1759,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1629])).

fof(f1629,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1628])).

fof(f1628,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1550])).

fof(f1550,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f2306,plain,
    ( spl17_54
    | ~ spl17_22
    | ~ spl17_38 ),
    inference(avatar_split_clause,[],[f2302,f2109,f2026,f2304])).

fof(f2026,plain,
    ( spl17_22
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_22])])).

fof(f2302,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))
    | ~ spl17_22
    | ~ spl17_38 ),
    inference(forward_demodulation,[],[f2027,f2110])).

fof(f2027,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl17_22 ),
    inference(avatar_component_clause,[],[f2026])).

fof(f2111,plain,
    ( spl17_38
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f2107,f1961,f1829,f2109])).

fof(f1829,plain,
    ( spl17_4
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f1961,plain,
    ( spl17_14
  <=> sK2 = sK16(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f2107,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(forward_demodulation,[],[f2105,f1962])).

fof(f1962,plain,
    ( sK2 = sK16(sK0,sK1,sK2)
    | ~ spl17_14 ),
    inference(avatar_component_clause,[],[f1961])).

fof(f2105,plain,
    ( sK0 = k1_relat_1(sK16(sK0,sK1,sK2))
    | ~ spl17_4 ),
    inference(resolution,[],[f1812,f1830])).

fof(f1830,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f1829])).

fof(f1812,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | k1_relat_1(sK16(X0,X1,X6)) = X0 ) ),
    inference(equality_resolution,[],[f1779])).

fof(f1779,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK16(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1687])).

fof(f1687,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK14(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK15(X0,X1,X2)),X1)
              & k1_relat_1(sK15(X0,X1,X2)) = X0
              & sK14(X0,X1,X2) = sK15(X0,X1,X2)
              & v1_funct_1(sK15(X0,X1,X2))
              & v1_relat_1(sK15(X0,X1,X2)) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK16(X0,X1,X6)),X1)
                & k1_relat_1(sK16(X0,X1,X6)) = X0
                & sK16(X0,X1,X6) = X6
                & v1_funct_1(sK16(X0,X1,X6))
                & v1_relat_1(sK16(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f1683,f1686,f1685,f1684])).

fof(f1684,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK14(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK14(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1685,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK14(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK15(X0,X1,X2)),X1)
        & k1_relat_1(sK15(X0,X1,X2)) = X0
        & sK14(X0,X1,X2) = sK15(X0,X1,X2)
        & v1_funct_1(sK15(X0,X1,X2))
        & v1_relat_1(sK15(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1686,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK16(X0,X1,X6)),X1)
        & k1_relat_1(sK16(X0,X1,X6)) = X0
        & sK16(X0,X1,X6) = X6
        & v1_funct_1(sK16(X0,X1,X6))
        & v1_relat_1(sK16(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1683,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1682])).

fof(f1682,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1477])).

fof(f1477,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f2104,plain,
    ( spl17_37
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f2100,f1961,f1829,f2102])).

fof(f2100,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(forward_demodulation,[],[f2098,f1962])).

fof(f2098,plain,
    ( r1_tarski(k2_relat_1(sK16(sK0,sK1,sK2)),sK1)
    | ~ spl17_4 ),
    inference(resolution,[],[f1811,f1830])).

fof(f1811,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK16(X0,X1,X6)),X1) ) ),
    inference(equality_resolution,[],[f1780])).

fof(f1780,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK16(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1687])).

fof(f2028,plain,
    ( spl17_22
    | ~ spl17_17 ),
    inference(avatar_split_clause,[],[f2013,f2000,f2026])).

fof(f2000,plain,
    ( spl17_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_17])])).

fof(f2013,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl17_17 ),
    inference(resolution,[],[f2001,f1693])).

fof(f1693,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1652])).

fof(f2001,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl17_17 ),
    inference(avatar_component_clause,[],[f2000])).

fof(f2002,plain,
    ( spl17_17
    | ~ spl17_1
    | ~ spl17_15 ),
    inference(avatar_split_clause,[],[f1998,f1968,f1819,f2000])).

fof(f1998,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl17_1
    | ~ spl17_15 ),
    inference(subsumption_resolution,[],[f1994,f1969])).

fof(f1994,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ spl17_1 ),
    inference(resolution,[],[f1763,f1975])).

fof(f1763,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1631])).

fof(f1631,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1630])).

fof(f1630,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1540])).

fof(f1540,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1976,plain,
    ( spl17_1
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f1974,f1961,f1829,f1819])).

fof(f1974,plain,
    ( v1_funct_1(sK2)
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f1965,f1830])).

fof(f1965,plain,
    ( v1_funct_1(sK2)
    | ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl17_14 ),
    inference(superposition,[],[f1814,f1962])).

fof(f1814,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK16(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1777])).

fof(f1777,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK16(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1687])).

fof(f1970,plain,
    ( spl17_15
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f1966,f1961,f1829,f1968])).

fof(f1966,plain,
    ( v1_relat_1(sK2)
    | ~ spl17_4
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f1964,f1830])).

fof(f1964,plain,
    ( v1_relat_1(sK2)
    | ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl17_14 ),
    inference(superposition,[],[f1815,f1962])).

fof(f1815,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK16(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f1776])).

fof(f1776,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK16(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1687])).

fof(f1963,plain,
    ( spl17_14
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f1958,f1829,f1961])).

fof(f1958,plain,
    ( sK2 = sK16(sK0,sK1,sK2)
    | ~ spl17_4 ),
    inference(resolution,[],[f1813,f1830])).

fof(f1813,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | sK16(X0,X1,X6) = X6 ) ),
    inference(equality_resolution,[],[f1778])).

fof(f1778,plain,(
    ! [X6,X2,X0,X1] :
      ( sK16(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1687])).

fof(f1831,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f1688,f1829])).

fof(f1688,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1649])).

fof(f1649,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1577,f1648])).

fof(f1648,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f1577,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f1515])).

fof(f1515,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f1514])).

fof(f1514,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f1827,plain,
    ( ~ spl17_1
    | ~ spl17_2
    | ~ spl17_3 ),
    inference(avatar_split_clause,[],[f1689,f1825,f1822,f1819])).

fof(f1689,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1649])).
%------------------------------------------------------------------------------
