%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1127+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  188 (2196 expanded)
%              Number of leaves         :   23 ( 686 expanded)
%              Depth                    :   19
%              Number of atoms          :  808 (11006 expanded)
%              Number of equality atoms :   27 ( 750 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2076,f2094,f2161,f2564,f2570,f2576,f2582,f2592,f2598,f2600,f2752,f3014,f3016,f3035,f3049,f3065,f3103,f3129,f3135,f3145])).

fof(f3145,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_66
    | spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3144])).

fof(f3144,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_66
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3143,f2502])).

fof(f2502,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(backward_demodulation,[],[f2387,f2499])).

fof(f2499,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(equality_resolution,[],[f2376])).

fof(f2376,plain,
    ( ! [X8,X9] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X8,X9)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X9 )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2372,f2085])).

fof(f2085,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ spl15_3 ),
    inference(resolution,[],[f2025,f1986])).

fof(f1986,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f1886])).

fof(f1886,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f2025,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f2024,plain,
    ( spl15_3
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f2372,plain,
    ( ! [X8,X9] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X8,X9)
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X9
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) )
    | ~ spl15_15 ),
    inference(superposition,[],[f1967,f2089])).

fof(f2089,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f2087])).

fof(f2087,plain,
    ( spl15_15
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1967,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1876])).

fof(f1876,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1806])).

fof(f1806,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f2387,plain,
    ( r2_hidden(u1_struct_0(sK2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(backward_demodulation,[],[f2162,f2378])).

fof(f2378,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(equality_resolution,[],[f2375])).

fof(f2375,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X4,X5)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X4 )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2370,f2085])).

fof(f2370,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X4,X5)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X4
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) )
    | ~ spl15_15 ),
    inference(superposition,[],[f1966,f2089])).

fof(f1966,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1876])).

fof(f2162,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl15_3 ),
    inference(resolution,[],[f2158,f1947])).

fof(f1947,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f1911,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),sK9(X0)),u1_pre_topc(X0))
          & r2_hidden(sK9(X0),u1_pre_topc(X0))
          & r2_hidden(sK8(X0),u1_pre_topc(X0))
          & m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) )
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
          & r1_tarski(sK10(X0),u1_pre_topc(X0))
          & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f1907,f1910,f1909,f1908])).

fof(f1908,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK8(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1909,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK8(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),sK9(X0)),u1_pre_topc(X0))
        & r2_hidden(sK9(X0),u1_pre_topc(X0))
        & r2_hidden(sK8(X0),u1_pre_topc(X0))
        & m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1910,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
        & r1_tarski(sK10(X0),u1_pre_topc(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1907,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f1906])).

fof(f1906,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f1905])).

fof(f1905,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f1887])).

fof(f1887,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2158,plain,
    ( sP0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl15_3 ),
    inference(subsumption_resolution,[],[f2156,f1923])).

fof(f1923,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f1891])).

fof(f1891,plain,
    ( ~ v2_pre_topc(sK2)
    & v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1855,f1890])).

fof(f1890,plain,
    ( ? [X0] :
        ( ~ v2_pre_topc(X0)
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & l1_pre_topc(X0) )
   => ( ~ v2_pre_topc(sK2)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1855,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1854])).

fof(f1854,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1847])).

fof(f1847,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => v2_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f1846])).

fof(f1846,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

fof(f2156,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | sP0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl15_3 ),
    inference(resolution,[],[f2078,f1945])).

fof(f1945,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_pre_topc(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1904,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f1888])).

fof(f1888,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2078,plain,
    ( sP1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl15_3 ),
    inference(resolution,[],[f2025,f1965])).

fof(f1965,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f1889])).

fof(f1889,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f1875,f1888,f1887])).

fof(f1875,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1874])).

fof(f1874,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1849])).

fof(f1849,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f1771])).

fof(f1771,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f3143,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_66
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3142,f2596])).

fof(f2596,plain,
    ( ~ r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | spl15_72 ),
    inference(avatar_component_clause,[],[f2595])).

fof(f2595,plain,
    ( spl15_72
  <=> r1_tarski(sK10(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f3142,plain,
    ( r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_66 ),
    inference(subsumption_resolution,[],[f3141,f2011])).

fof(f2011,plain,(
    ~ sP0(sK2) ),
    inference(subsumption_resolution,[],[f2010,f1924])).

fof(f1924,plain,(
    ~ v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f1891])).

fof(f2010,plain,
    ( ~ sP0(sK2)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f1992,f1946])).

fof(f1946,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1992,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f1922,f1965])).

fof(f1922,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f1891])).

fof(f3141,plain,
    ( sP0(sK2)
    | r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_66 ),
    inference(resolution,[],[f2562,f1951])).

fof(f1951,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0)
      | r1_tarski(sK10(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2562,plain,
    ( ~ m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl15_66 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f2561,plain,
    ( spl15_66
  <=> m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_66])])).

fof(f3135,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_67
    | spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3134])).

fof(f3134,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_67
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3133,f2502])).

fof(f3133,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_67
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3132,f2596])).

fof(f3132,plain,
    ( r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_67 ),
    inference(subsumption_resolution,[],[f3131,f2011])).

fof(f3131,plain,
    ( sP0(sK2)
    | r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_67 ),
    inference(resolution,[],[f2568,f1954])).

fof(f1954,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0)
      | r1_tarski(sK10(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2568,plain,
    ( ~ m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl15_67 ),
    inference(avatar_component_clause,[],[f2567])).

fof(f2567,plain,
    ( spl15_67
  <=> m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_67])])).

fof(f3129,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_68
    | spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3128])).

fof(f3128,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_68
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3105,f2574])).

fof(f2574,plain,
    ( ~ r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | spl15_68 ),
    inference(avatar_component_clause,[],[f2573])).

fof(f2573,plain,
    ( spl15_68
  <=> r2_hidden(sK8(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_68])])).

fof(f3105,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3104,f2502])).

fof(f3104,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3098,f2011])).

fof(f3098,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_72 ),
    inference(resolution,[],[f2596,f1957])).

fof(f1957,plain,(
    ! [X0] :
      ( r1_tarski(sK10(X0),u1_pre_topc(X0))
      | r2_hidden(sK8(X0),u1_pre_topc(X0))
      | sP0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f3103,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_69
    | spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3102])).

fof(f3102,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_69
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3101,f2502])).

fof(f3101,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_69
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3100,f2011])).

fof(f3100,plain,
    ( sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_69
    | spl15_72 ),
    inference(subsumption_resolution,[],[f3099,f2580])).

fof(f2580,plain,
    ( ~ r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | spl15_69 ),
    inference(avatar_component_clause,[],[f2579])).

fof(f2579,plain,
    ( spl15_69
  <=> r2_hidden(sK9(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_69])])).

fof(f3099,plain,
    ( r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl15_72 ),
    inference(resolution,[],[f2596,f1960])).

fof(f1960,plain,(
    ! [X0] :
      ( r1_tarski(sK10(X0),u1_pre_topc(X0))
      | r2_hidden(sK9(X0),u1_pre_topc(X0))
      | sP0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f3065,plain,
    ( ~ spl15_72
    | ~ spl15_70
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65 ),
    inference(avatar_split_clause,[],[f2720,f2557,f2087,f2024,f2585,f2595])).

fof(f2585,plain,
    ( spl15_70
  <=> m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).

fof(f2557,plain,
    ( spl15_65
  <=> r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_65])])).

fof(f2720,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65 ),
    inference(resolution,[],[f2522,f2559])).

fof(f2559,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | spl15_65 ),
    inference(avatar_component_clause,[],[f2557])).

fof(f2522,plain,
    ( ! [X0] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK2),X0),u1_pre_topc(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ r1_tarski(X0,u1_pre_topc(sK2)) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f2521,f2378])).

fof(f2521,plain,
    ( ! [X0] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK2),X0),u1_pre_topc(sK2))
        | ~ r1_tarski(X0,u1_pre_topc(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f2520,f2378])).

fof(f2520,plain,
    ( ! [X0] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0),u1_pre_topc(sK2))
        | ~ r1_tarski(X0,u1_pre_topc(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2504,f2158])).

fof(f2504,plain,
    ( ! [X0] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0),u1_pre_topc(sK2))
        | ~ r1_tarski(X0,u1_pre_topc(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
        | ~ sP0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(superposition,[],[f1948,f2499])).

fof(f1948,plain,(
    ! [X6,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
      | ~ r1_tarski(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f3049,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_67
    | ~ spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3048])).

fof(f3048,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_67
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2731,f2568])).

fof(f2731,plain,
    ( m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2730,f2502])).

fof(f2730,plain,
    ( m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2725,f2011])).

fof(f2725,plain,
    ( m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(resolution,[],[f2722,f1953])).

fof(f1953,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2722,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2720,f2597])).

fof(f2597,plain,
    ( r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ spl15_72 ),
    inference(avatar_component_clause,[],[f2595])).

fof(f3035,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_68
    | ~ spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3034])).

fof(f3034,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_68
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2733,f2574])).

fof(f2733,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2732,f2502])).

fof(f2732,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2726,f2011])).

fof(f2726,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(resolution,[],[f2722,f1956])).

fof(f1956,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK8(X0),u1_pre_topc(X0))
      | sP0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f3016,plain,
    ( ~ spl15_68
    | ~ spl15_69
    | ~ spl15_3
    | ~ spl15_15
    | ~ spl15_66
    | ~ spl15_67
    | spl15_71 ),
    inference(avatar_split_clause,[],[f2954,f2589,f2567,f2561,f2087,f2024,f2579,f2573])).

fof(f2589,plain,
    ( spl15_71
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_71])])).

fof(f2954,plain,
    ( ~ r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | ~ spl15_66
    | ~ spl15_67
    | spl15_71 ),
    inference(subsumption_resolution,[],[f2953,f2563])).

fof(f2563,plain,
    ( m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_66 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f2953,plain,
    ( ~ m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | ~ spl15_67
    | spl15_71 ),
    inference(subsumption_resolution,[],[f2951,f2569])).

fof(f2569,plain,
    ( m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_67 ),
    inference(avatar_component_clause,[],[f2567])).

fof(f2951,plain,
    ( ~ m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_71 ),
    inference(resolution,[],[f2526,f2591])).

fof(f2591,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | spl15_71 ),
    inference(avatar_component_clause,[],[f2589])).

fof(f2526,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK2),X1,X2),u1_pre_topc(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X2,u1_pre_topc(sK2))
        | ~ r2_hidden(X1,u1_pre_topc(sK2)) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f2525,f2378])).

fof(f2525,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK2),X1,X2),u1_pre_topc(sK2))
        | ~ r2_hidden(X2,u1_pre_topc(sK2))
        | ~ r2_hidden(X1,u1_pre_topc(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f2524,f2378])).

fof(f2524,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK2),X1,X2),u1_pre_topc(sK2))
        | ~ r2_hidden(X2,u1_pre_topc(sK2))
        | ~ r2_hidden(X1,u1_pre_topc(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f2523,f2378])).

fof(f2523,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X1,X2),u1_pre_topc(sK2))
        | ~ r2_hidden(X2,u1_pre_topc(sK2))
        | ~ r2_hidden(X1,u1_pre_topc(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2505,f2158])).

fof(f2505,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X1,X2),u1_pre_topc(sK2))
        | ~ r2_hidden(X2,u1_pre_topc(sK2))
        | ~ r2_hidden(X1,u1_pre_topc(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | ~ sP0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(superposition,[],[f1949,f2499])).

fof(f1949,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f3014,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_69
    | ~ spl15_72 ),
    inference(avatar_contradiction_clause,[],[f3013])).

fof(f3013,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_69
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2735,f2580])).

fof(f2735,plain,
    ( r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2734,f2502])).

fof(f2734,plain,
    ( r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2727,f2011])).

fof(f2727,plain,
    ( r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(resolution,[],[f2722,f1959])).

fof(f1959,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK9(X0),u1_pre_topc(X0))
      | sP0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2752,plain,
    ( ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_66
    | ~ spl15_72 ),
    inference(avatar_contradiction_clause,[],[f2751])).

fof(f2751,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | spl15_66
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2729,f2562])).

fof(f2729,plain,
    ( m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2728,f2502])).

fof(f2728,plain,
    ( m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f2724,f2011])).

fof(f2724,plain,
    ( m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sP0(sK2)
    | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15
    | spl15_65
    | ~ spl15_72 ),
    inference(resolution,[],[f2722,f1950])).

fof(f1950,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2600,plain,
    ( ~ spl15_65
    | ~ spl15_71
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2599,f2087,f2024,f2589,f2557])).

fof(f2599,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2553,f2011])).

fof(f2553,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1964])).

fof(f1964,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),sK9(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2598,plain,
    ( spl15_72
    | ~ spl15_71
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2593,f2087,f2024,f2589,f2595])).

fof(f2593,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2552,f2011])).

fof(f2552,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | r1_tarski(sK10(sK2),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1963])).

fof(f1963,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),sK9(X0)),u1_pre_topc(X0))
      | r1_tarski(sK10(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2592,plain,
    ( spl15_70
    | ~ spl15_71
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2583,f2087,f2024,f2589,f2585])).

fof(f2583,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2551,f2011])).

fof(f2551,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK2),sK8(sK2),sK9(sK2)),u1_pre_topc(sK2))
    | m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1962])).

fof(f1962,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK8(X0),sK9(X0)),u1_pre_topc(X0))
      | m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2582,plain,
    ( ~ spl15_65
    | spl15_69
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2577,f2087,f2024,f2579,f2557])).

fof(f2577,plain,
    ( r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2550,f2011])).

fof(f2550,plain,
    ( r2_hidden(sK9(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1961])).

fof(f1961,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r2_hidden(sK9(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2576,plain,
    ( ~ spl15_65
    | spl15_68
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2571,f2087,f2024,f2573,f2557])).

fof(f2571,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2549,f2011])).

fof(f2549,plain,
    ( r2_hidden(sK8(sK2),u1_pre_topc(sK2))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1958])).

fof(f1958,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r2_hidden(sK8(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2570,plain,
    ( ~ spl15_65
    | spl15_67
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2565,f2087,f2024,f2567,f2557])).

fof(f2565,plain,
    ( m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2548,f2011])).

fof(f2548,plain,
    ( m1_subset_1(sK9(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1955])).

fof(f1955,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2564,plain,
    ( ~ spl15_65
    | spl15_66
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f2555,f2087,f2024,f2561,f2557])).

fof(f2555,plain,
    ( m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f2547,f2011])).

fof(f2547,plain,
    ( m1_subset_1(sK8(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK2),sK10(sK2)),u1_pre_topc(sK2))
    | sP0(sK2)
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(resolution,[],[f2502,f1952])).

fof(f1952,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2161,plain,(
    spl15_16 ),
    inference(avatar_contradiction_clause,[],[f2160])).

fof(f2160,plain,
    ( $false
    | spl15_16 ),
    inference(subsumption_resolution,[],[f2093,f2073])).

fof(f2073,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f1999,f1968])).

fof(f1968,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1877])).

fof(f1877,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f1999,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f1922,f1986])).

fof(f2093,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl15_16 ),
    inference(avatar_component_clause,[],[f2091])).

fof(f2091,plain,
    ( spl15_16
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f2094,plain,
    ( spl15_15
    | ~ spl15_16
    | ~ spl15_3 ),
    inference(avatar_split_clause,[],[f2080,f2024,f2091,f2087])).

fof(f2080,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl15_3 ),
    inference(resolution,[],[f2025,f1973])).

fof(f1973,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f1883])).

fof(f1883,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1882])).

fof(f1882,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f2076,plain,(
    spl15_3 ),
    inference(avatar_contradiction_clause,[],[f2075])).

fof(f2075,plain,
    ( $false
    | spl15_3 ),
    inference(subsumption_resolution,[],[f2074,f2026])).

fof(f2026,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl15_3 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f2074,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f1999,f1969])).

fof(f1969,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1877])).
%------------------------------------------------------------------------------
