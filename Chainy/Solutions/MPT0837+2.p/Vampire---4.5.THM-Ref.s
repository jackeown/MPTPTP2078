%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0837+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 138 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  307 ( 628 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1781,f1786,f1794,f2850,f2924,f2932,f2936,f3038,f3224,f3246,f3481])).

fof(f3481,plain,
    ( ~ spl66_5
    | ~ spl66_89
    | spl66_105 ),
    inference(avatar_contradiction_clause,[],[f3480])).

fof(f3480,plain,
    ( $false
    | ~ spl66_5
    | ~ spl66_89
    | spl66_105 ),
    inference(subsumption_resolution,[],[f3478,f3245])).

fof(f3245,plain,
    ( ~ r2_hidden(sK30(sK2,sK3),sK1)
    | spl66_105 ),
    inference(avatar_component_clause,[],[f3244])).

fof(f3244,plain,
    ( spl66_105
  <=> r2_hidden(sK30(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_105])])).

fof(f3478,plain,
    ( r2_hidden(sK30(sK2,sK3),sK1)
    | ~ spl66_5
    | ~ spl66_89 ),
    inference(resolution,[],[f2373,f2943])).

fof(f2943,plain,
    ( r2_hidden(k4_tarski(sK30(sK2,sK3),sK3),sK2)
    | ~ spl66_89 ),
    inference(avatar_component_clause,[],[f2942])).

fof(f2942,plain,
    ( spl66_89
  <=> r2_hidden(k4_tarski(sK30(sK2,sK3),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_89])])).

fof(f2373,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(X5,X6),sK2)
        | r2_hidden(X5,sK1) )
    | ~ spl66_5 ),
    inference(resolution,[],[f2257,f1547])).

fof(f1547,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1413])).

fof(f1413,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1412])).

fof(f1412,plain,(
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

fof(f2257,plain,
    ( ! [X10] :
        ( r2_hidden(X10,k2_zfmisc_1(sK1,sK0))
        | ~ r2_hidden(X10,sK2) )
    | ~ spl66_5 ),
    inference(resolution,[],[f1660,f1793])).

fof(f1793,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl66_5 ),
    inference(avatar_component_clause,[],[f1792])).

fof(f1792,plain,
    ( spl66_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_5])])).

fof(f1660,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1322])).

fof(f1322,plain,(
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

fof(f3246,plain,
    ( ~ spl66_105
    | spl66_103 ),
    inference(avatar_split_clause,[],[f3242,f3222,f3244])).

fof(f3222,plain,
    ( spl66_103
  <=> m1_subset_1(sK30(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_103])])).

fof(f3242,plain,
    ( ~ r2_hidden(sK30(sK2,sK3),sK1)
    | spl66_103 ),
    inference(resolution,[],[f3223,f1640])).

fof(f1640,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1311])).

fof(f1311,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f3223,plain,
    ( ~ m1_subset_1(sK30(sK2,sK3),sK1)
    | spl66_103 ),
    inference(avatar_component_clause,[],[f3222])).

fof(f3224,plain,
    ( ~ spl66_103
    | ~ spl66_2
    | ~ spl66_89 ),
    inference(avatar_split_clause,[],[f3216,f2942,f1779,f3222])).

fof(f1779,plain,
    ( spl66_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_2])])).

fof(f3216,plain,
    ( ~ m1_subset_1(sK30(sK2,sK3),sK1)
    | ~ spl66_2
    | ~ spl66_89 ),
    inference(resolution,[],[f2943,f1780])).

fof(f1780,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl66_2 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f3038,plain,
    ( spl66_89
    | ~ spl66_87 ),
    inference(avatar_split_clause,[],[f3034,f2922,f2942])).

fof(f2922,plain,
    ( spl66_87
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_87])])).

fof(f3034,plain,
    ( r2_hidden(k4_tarski(sK30(sK2,sK3),sK3),sK2)
    | ~ spl66_87 ),
    inference(resolution,[],[f2935,f1762])).

fof(f1762,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK30(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f1581])).

fof(f1581,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK30(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1442])).

fof(f1442,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK28(X0,X1)),X0)
            | ~ r2_hidden(sK28(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK29(X0,X1),sK28(X0,X1)),X0)
            | r2_hidden(sK28(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK30(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f1438,f1441,f1440,f1439])).

fof(f1439,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK28(X0,X1)),X0)
          | ~ r2_hidden(sK28(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK28(X0,X1)),X0)
          | r2_hidden(sK28(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1440,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK28(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK29(X0,X1),sK28(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1441,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK30(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1438,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1437])).

fof(f1437,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f657])).

fof(f657,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f2935,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl66_87 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f2936,plain,
    ( spl66_87
    | ~ spl66_1
    | ~ spl66_83 ),
    inference(avatar_split_clause,[],[f2934,f2848,f1776,f2922])).

fof(f1776,plain,
    ( spl66_1
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_1])])).

fof(f2848,plain,
    ( spl66_83
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_83])])).

fof(f2934,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl66_1
    | ~ spl66_83 ),
    inference(forward_demodulation,[],[f1782,f2849])).

fof(f2849,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl66_83 ),
    inference(avatar_component_clause,[],[f2848])).

fof(f1782,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl66_1 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f2932,plain,
    ( ~ spl66_3
    | spl66_87 ),
    inference(avatar_contradiction_clause,[],[f2930])).

fof(f2930,plain,
    ( $false
    | ~ spl66_3
    | spl66_87 ),
    inference(unit_resulting_resolution,[],[f1785,f2923,f1761])).

fof(f1761,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f1582])).

fof(f1582,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1442])).

fof(f2923,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl66_87 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f1785,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl66_3 ),
    inference(avatar_component_clause,[],[f1784])).

fof(f1784,plain,
    ( spl66_3
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl66_3])])).

fof(f2924,plain,
    ( ~ spl66_87
    | spl66_1
    | ~ spl66_83 ),
    inference(avatar_split_clause,[],[f2919,f2848,f1776,f2922])).

fof(f2919,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl66_1
    | ~ spl66_83 ),
    inference(backward_demodulation,[],[f1777,f2849])).

fof(f1777,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl66_1 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f2850,plain,
    ( spl66_83
    | ~ spl66_5 ),
    inference(avatar_split_clause,[],[f2840,f1792,f2848])).

fof(f2840,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl66_5 ),
    inference(resolution,[],[f1639,f1793])).

fof(f1639,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1310])).

fof(f1310,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1225])).

fof(f1225,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1794,plain,(
    spl66_5 ),
    inference(avatar_split_clause,[],[f1523,f1792])).

fof(f1523,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1395,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1389,f1394,f1393,f1392,f1391,f1390])).

fof(f1390,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X5,X3),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,sK0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,sK0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1391,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k2_relset_1(X1,sK0,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X5,X3),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k2_relset_1(X1,sK0,X2)) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                    | ~ m1_subset_1(X4,sK1) )
                | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X5,X3),X2)
                    & m1_subset_1(X5,sK1) )
                | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1392,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,sK1) )
              | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,sK1) )
              | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1393,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,X3),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,sK3),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1394,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1389,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f1388])).

fof(f1388,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f1264])).

fof(f1264,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1258])).

fof(f1258,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1257])).

fof(f1257,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(f1786,plain,
    ( spl66_1
    | spl66_3 ),
    inference(avatar_split_clause,[],[f1525,f1784,f1776])).

fof(f1525,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1781,plain,
    ( ~ spl66_1
    | spl66_2 ),
    inference(avatar_split_clause,[],[f1526,f1779,f1776])).

fof(f1526,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f1395])).
%------------------------------------------------------------------------------
