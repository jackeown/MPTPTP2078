%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0836+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 141 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 700 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3518,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1770,f1775,f1787,f2851,f2857,f2865,f2869,f2962,f3181,f3199,f3517])).

fof(f3517,plain,
    ( ~ spl66_6
    | ~ spl66_88
    | spl66_105 ),
    inference(avatar_contradiction_clause,[],[f3516])).

fof(f3516,plain,
    ( $false
    | ~ spl66_6
    | ~ spl66_88
    | spl66_105 ),
    inference(subsumption_resolution,[],[f3514,f3198])).

fof(f3198,plain,
    ( ~ r2_hidden(sK27(sK2,sK3),sK1)
    | spl66_105 ),
    inference(avatar_component_clause,[],[f3197])).

fof(f3197,plain,
    ( spl66_105
  <=> r2_hidden(sK27(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_105])])).

fof(f3514,plain,
    ( r2_hidden(sK27(sK2,sK3),sK1)
    | ~ spl66_6
    | ~ spl66_88 ),
    inference(resolution,[],[f2386,f2876])).

fof(f2876,plain,
    ( r2_hidden(k4_tarski(sK3,sK27(sK2,sK3)),sK2)
    | ~ spl66_88 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f2875,plain,
    ( spl66_88
  <=> r2_hidden(k4_tarski(sK3,sK27(sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_88])])).

fof(f2386,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
        | r2_hidden(X4,sK1) )
    | ~ spl66_6 ),
    inference(resolution,[],[f2253,f1543])).

fof(f1543,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1406])).

fof(f1406,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f2253,plain,
    ( ! [X10] :
        ( r2_hidden(X10,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X10,sK2) )
    | ~ spl66_6 ),
    inference(resolution,[],[f1649,f1786])).

fof(f1786,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl66_6 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f1785,plain,
    ( spl66_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_6])])).

fof(f1649,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1315])).

fof(f1315,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f3199,plain,
    ( ~ spl66_105
    | spl66_103 ),
    inference(avatar_split_clause,[],[f3195,f3179,f3197])).

fof(f3179,plain,
    ( spl66_103
  <=> m1_subset_1(sK27(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_103])])).

fof(f3195,plain,
    ( ~ r2_hidden(sK27(sK2,sK3),sK1)
    | spl66_103 ),
    inference(resolution,[],[f3180,f1629])).

fof(f1629,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f1304,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f3180,plain,
    ( ~ m1_subset_1(sK27(sK2,sK3),sK1)
    | spl66_103 ),
    inference(avatar_component_clause,[],[f3179])).

fof(f3181,plain,
    ( ~ spl66_103
    | ~ spl66_2
    | ~ spl66_88 ),
    inference(avatar_split_clause,[],[f3174,f2875,f1768,f3179])).

fof(f1768,plain,
    ( spl66_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_2])])).

fof(f3174,plain,
    ( ~ m1_subset_1(sK27(sK2,sK3),sK1)
    | ~ spl66_2
    | ~ spl66_88 ),
    inference(resolution,[],[f2876,f1769])).

fof(f1769,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl66_2 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f2962,plain,
    ( spl66_88
    | ~ spl66_86 ),
    inference(avatar_split_clause,[],[f2958,f2855,f2875])).

fof(f2855,plain,
    ( spl66_86
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_86])])).

fof(f2958,plain,
    ( r2_hidden(k4_tarski(sK3,sK27(sK2,sK3)),sK2)
    | ~ spl66_86 ),
    inference(resolution,[],[f2868,f1749])).

fof(f1749,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK27(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f1572])).

fof(f1572,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK27(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK25(X0,X1),X3),X0)
            | ~ r2_hidden(sK25(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK25(X0,X1),sK26(X0,X1)),X0)
            | r2_hidden(sK25(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK27(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27])],[f1426,f1429,f1428,f1427])).

fof(f1427,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK25(X0,X1),X3),X0)
          | ~ r2_hidden(sK25(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK25(X0,X1),X4),X0)
          | r2_hidden(sK25(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1428,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK25(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK25(X0,X1),sK26(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1429,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK27(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1426,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1425])).

fof(f1425,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f2868,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl66_86 ),
    inference(avatar_component_clause,[],[f2855])).

fof(f2869,plain,
    ( spl66_86
    | ~ spl66_1
    | ~ spl66_85 ),
    inference(avatar_split_clause,[],[f2867,f2849,f1765,f2855])).

fof(f1765,plain,
    ( spl66_1
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_1])])).

fof(f2849,plain,
    ( spl66_85
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_85])])).

fof(f2867,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl66_1
    | ~ spl66_85 ),
    inference(forward_demodulation,[],[f1771,f2850])).

fof(f2850,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl66_85 ),
    inference(avatar_component_clause,[],[f2849])).

fof(f1771,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl66_1 ),
    inference(avatar_component_clause,[],[f1765])).

fof(f2865,plain,
    ( ~ spl66_3
    | spl66_86 ),
    inference(avatar_contradiction_clause,[],[f2863])).

fof(f2863,plain,
    ( $false
    | ~ spl66_3
    | spl66_86 ),
    inference(unit_resulting_resolution,[],[f1774,f2856,f1748])).

fof(f1748,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f1573])).

fof(f1573,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f2856,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl66_86 ),
    inference(avatar_component_clause,[],[f2855])).

fof(f1774,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl66_3 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1773,plain,
    ( spl66_3
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_3])])).

fof(f2857,plain,
    ( ~ spl66_86
    | spl66_1
    | ~ spl66_85 ),
    inference(avatar_split_clause,[],[f2852,f2849,f1765,f2855])).

fof(f2852,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl66_1
    | ~ spl66_85 ),
    inference(backward_demodulation,[],[f1766,f2850])).

fof(f1766,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl66_1 ),
    inference(avatar_component_clause,[],[f1765])).

fof(f2851,plain,
    ( spl66_85
    | ~ spl66_6 ),
    inference(avatar_split_clause,[],[f2841,f1785,f2849])).

fof(f2841,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl66_6 ),
    inference(resolution,[],[f1628,f1786])).

fof(f1628,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1303])).

fof(f1303,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1224])).

fof(f1224,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1787,plain,(
    spl66_6 ),
    inference(avatar_split_clause,[],[f1517,f1785])).

fof(f1517,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1389])).

fof(f1389,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK3,sK4),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1383,f1388,f1387,f1386,f1385,f1384])).

fof(f1384,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X3,X5),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1385,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X3,X5),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                & m1_subset_1(X3,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ m1_subset_1(X4,sK1) )
                | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X3,X5),X2)
                    & m1_subset_1(X5,sK1) )
                | r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1386,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                  | ~ m1_subset_1(X4,sK1) )
              | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),X2)
                  & m1_subset_1(X5,sK1) )
              | r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f1387,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X3,X5),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & m1_subset_1(X3,sK0) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(sK3,X5),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1388,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(sK3,X5),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK3,sK4),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1383,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f1382])).

fof(f1382,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1381])).

fof(f1381,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f1263])).

fof(f1263,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1257])).

fof(f1257,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1256])).

fof(f1256,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

fof(f1775,plain,
    ( spl66_1
    | spl66_3 ),
    inference(avatar_split_clause,[],[f1520,f1773,f1765])).

fof(f1520,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1389])).

fof(f1770,plain,
    ( ~ spl66_1
    | spl66_2 ),
    inference(avatar_split_clause,[],[f1521,f1768,f1765])).

fof(f1521,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f1389])).
%------------------------------------------------------------------------------
