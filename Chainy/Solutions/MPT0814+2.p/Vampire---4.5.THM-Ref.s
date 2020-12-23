%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0814+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 3.57s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  156 ( 311 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3937,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1656,f1660,f2883,f3382,f3872,f3936])).

fof(f3936,plain,
    ( ~ spl60_1
    | ~ spl60_2
    | ~ spl60_76
    | spl60_86 ),
    inference(avatar_contradiction_clause,[],[f3935])).

fof(f3935,plain,
    ( $false
    | ~ spl60_1
    | ~ spl60_2
    | ~ spl60_76
    | spl60_86 ),
    inference(subsumption_resolution,[],[f3934,f3378])).

fof(f3378,plain,
    ( ~ r2_hidden(sK53(sK0),sK2)
    | spl60_86 ),
    inference(avatar_component_clause,[],[f3377])).

fof(f3377,plain,
    ( spl60_86
  <=> r2_hidden(sK53(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_86])])).

fof(f3934,plain,
    ( r2_hidden(sK53(sK0),sK2)
    | ~ spl60_1
    | ~ spl60_2
    | ~ spl60_76 ),
    inference(subsumption_resolution,[],[f3933,f1655])).

fof(f1655,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl60_1 ),
    inference(avatar_component_clause,[],[f1654])).

fof(f1654,plain,
    ( spl60_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_1])])).

fof(f3933,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK53(sK0),sK2)
    | ~ spl60_2
    | ~ spl60_76 ),
    inference(superposition,[],[f1921,f2882])).

fof(f2882,plain,
    ( sK0 = k4_tarski(sK52(sK0),sK53(sK0))
    | ~ spl60_76 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f2881,plain,
    ( spl60_76
  <=> sK0 = k4_tarski(sK52(sK0),sK53(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_76])])).

fof(f1921,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X1),sK3)
        | r2_hidden(X1,sK2) )
    | ~ spl60_2 ),
    inference(resolution,[],[f1546,f1885])).

fof(f1885,plain,
    ( ! [X14] :
        ( r2_hidden(X14,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X14,sK3) )
    | ~ spl60_2 ),
    inference(resolution,[],[f1508,f1659])).

fof(f1659,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl60_2 ),
    inference(avatar_component_clause,[],[f1658])).

fof(f1658,plain,
    ( spl60_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_2])])).

fof(f1508,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1254])).

fof(f1254,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1546,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1403])).

fof(f1403,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1402])).

fof(f1402,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f3872,plain,
    ( spl60_87
    | ~ spl60_1
    | ~ spl60_2
    | ~ spl60_76 ),
    inference(avatar_split_clause,[],[f3870,f2881,f1658,f1654,f3380])).

fof(f3380,plain,
    ( spl60_87
  <=> r2_hidden(sK52(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_87])])).

fof(f3870,plain,
    ( r2_hidden(sK52(sK0),sK1)
    | ~ spl60_1
    | ~ spl60_2
    | ~ spl60_76 ),
    inference(subsumption_resolution,[],[f3869,f1655])).

fof(f3869,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK52(sK0),sK1)
    | ~ spl60_2
    | ~ spl60_76 ),
    inference(superposition,[],[f1908,f2882])).

fof(f1908,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),sK3)
        | r2_hidden(X1,sK1) )
    | ~ spl60_2 ),
    inference(resolution,[],[f1545,f1885])).

fof(f1545,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1403])).

fof(f3382,plain,
    ( ~ spl60_86
    | ~ spl60_87
    | ~ spl60_76 ),
    inference(avatar_split_clause,[],[f3375,f2881,f3380,f3377])).

fof(f3375,plain,
    ( ~ r2_hidden(sK52(sK0),sK1)
    | ~ r2_hidden(sK53(sK0),sK2)
    | ~ spl60_76 ),
    inference(trivial_inequality_removal,[],[f3349])).

fof(f3349,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK52(sK0),sK1)
    | ~ r2_hidden(sK53(sK0),sK2)
    | ~ spl60_76 ),
    inference(superposition,[],[f1423,f2882])).

fof(f1423,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f1310])).

fof(f1310,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1)
        | k4_tarski(X4,X5) != sK0 )
    & r2_hidden(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1217,f1309])).

fof(f1309,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1)
          | k4_tarski(X4,X5) != sK0 )
      & r2_hidden(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f1217,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f1216])).

fof(f1216,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f1214,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f1213])).

fof(f1213,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f2883,plain,
    ( spl60_76
    | ~ spl60_1
    | ~ spl60_2 ),
    inference(avatar_split_clause,[],[f2875,f1658,f1654,f2881])).

fof(f2875,plain,
    ( sK0 = k4_tarski(sK52(sK0),sK53(sK0))
    | ~ spl60_1
    | ~ spl60_2 ),
    inference(resolution,[],[f2510,f1655])).

fof(f2510,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | k4_tarski(sK52(X0),sK53(X0)) = X0 )
    | ~ spl60_2 ),
    inference(resolution,[],[f1885,f1568])).

fof(f1568,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK52(X0),sK53(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1410,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK52(X0),sK53(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK52,sK53])],[f1289,f1409])).

fof(f1409,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK52(X0),sK53(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f1289,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f300])).

fof(f300,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f1660,plain,(
    spl60_2 ),
    inference(avatar_split_clause,[],[f1421,f1658])).

fof(f1421,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f1310])).

fof(f1656,plain,(
    spl60_1 ),
    inference(avatar_split_clause,[],[f1422,f1654])).

fof(f1422,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f1310])).
%------------------------------------------------------------------------------
