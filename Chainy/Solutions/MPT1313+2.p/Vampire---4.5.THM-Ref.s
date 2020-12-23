%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1313+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:17 EST 2020

% Result     : Theorem 13.32s
% Output     : Refutation 13.32s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 341 expanded)
%              Number of leaves         :   26 ( 148 expanded)
%              Depth                    :   17
%              Number of atoms          :  685 (2185 expanded)
%              Number of equality atoms :   68 ( 299 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9063,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2916,f2929,f2966,f3086,f3156,f3253,f3257,f3262,f3324,f4144,f5774,f6555,f6646,f7249,f8472,f8909,f9062])).

fof(f9062,plain,
    ( ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_7
    | ~ spl43_8
    | spl43_20
    | ~ spl43_48 ),
    inference(avatar_contradiction_clause,[],[f9061])).

fof(f9061,plain,
    ( $false
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_7
    | ~ spl43_8
    | spl43_20
    | ~ spl43_48 ),
    inference(subsumption_resolution,[],[f9060,f3322])).

fof(f3322,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | spl43_20 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f3321,plain,
    ( spl43_20
  <=> r2_hidden(sK4,u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_20])])).

fof(f9060,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_7
    | ~ spl43_8
    | ~ spl43_48 ),
    inference(subsumption_resolution,[],[f9059,f4143])).

fof(f4143,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK2))
    | ~ spl43_48 ),
    inference(avatar_component_clause,[],[f4141])).

fof(f4141,plain,
    ( spl43_48
  <=> r2_hidden(sK5,u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_48])])).

fof(f9059,plain,
    ( ~ r2_hidden(sK5,u1_pre_topc(sK2))
    | r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_7
    | ~ spl43_8 ),
    inference(subsumption_resolution,[],[f9058,f3155])).

fof(f3155,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl43_7 ),
    inference(avatar_component_clause,[],[f3153])).

fof(f3153,plain,
    ( spl43_7
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_7])])).

fof(f9058,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK5,u1_pre_topc(sK2))
    | r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_8 ),
    inference(subsumption_resolution,[],[f9057,f2965])).

fof(f2965,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl43_3 ),
    inference(avatar_component_clause,[],[f2963])).

fof(f2963,plain,
    ( spl43_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_3])])).

fof(f9057,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK5,u1_pre_topc(sK2))
    | r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_8 ),
    inference(superposition,[],[f2960,f3252])).

fof(f3252,plain,
    ( sK4 = k9_subset_1(u1_struct_0(sK3),sK5,k2_struct_0(sK3))
    | ~ spl43_8 ),
    inference(avatar_component_clause,[],[f3250])).

fof(f3250,plain,
    ( spl43_8
  <=> sK4 = k9_subset_1(u1_struct_0(sK3),sK5,k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_8])])).

fof(f2960,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X9,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X9,u1_pre_topc(sK2))
        | r2_hidden(k9_subset_1(u1_struct_0(sK3),X9,k2_struct_0(sK3)),u1_pre_topc(sK3)) )
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(subsumption_resolution,[],[f2959,f2915])).

fof(f2915,plain,
    ( l1_pre_topc(sK2)
    | ~ spl43_1 ),
    inference(avatar_component_clause,[],[f2913])).

fof(f2913,plain,
    ( spl43_1
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_1])])).

fof(f2959,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,u1_pre_topc(sK2))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X9,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK3),X9,k2_struct_0(sK3)),u1_pre_topc(sK3))
        | ~ l1_pre_topc(sK2) )
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(subsumption_resolution,[],[f2942,f2952])).

fof(f2952,plain,
    ( l1_pre_topc(sK3)
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(subsumption_resolution,[],[f2938,f2915])).

fof(f2938,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl43_2 ),
    inference(resolution,[],[f2928,f2892])).

fof(f2892,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2541])).

fof(f2541,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2928,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl43_2 ),
    inference(avatar_component_clause,[],[f2926])).

fof(f2926,plain,
    ( spl43_2
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_2])])).

fof(f2942,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,u1_pre_topc(sK2))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X9,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK3),X9,k2_struct_0(sK3)),u1_pre_topc(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK2) )
    | ~ spl43_2 ),
    inference(resolution,[],[f2928,f2903])).

fof(f2903,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2724])).

fof(f2724,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2589])).

fof(f2589,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK13(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK13(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK13(X0,X1) = k9_subset_1(u1_struct_0(X1),sK14(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK14(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK14(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK13(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK13(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK15(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK15(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK15(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f2585,f2588,f2587,f2586])).

fof(f2586,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK13(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK13(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK13(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK13(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK13(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2587,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK13(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK13(X0,X1) = k9_subset_1(u1_struct_0(X1),sK14(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK14(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK14(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2588,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK15(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK15(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK15(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2585,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2584])).

fof(f2584,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2583])).

fof(f2583,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2421])).

fof(f2421,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1776])).

fof(f1776,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f8909,plain,
    ( ~ spl43_9
    | ~ spl43_134
    | ~ spl43_154
    | ~ spl43_294 ),
    inference(avatar_contradiction_clause,[],[f8908])).

fof(f8908,plain,
    ( $false
    | ~ spl43_9
    | ~ spl43_134
    | ~ spl43_154
    | ~ spl43_294 ),
    inference(subsumption_resolution,[],[f8907,f7248])).

fof(f7248,plain,
    ( sK4 = k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,sK4),k2_struct_0(sK3))
    | ~ spl43_154 ),
    inference(avatar_component_clause,[],[f7246])).

fof(f7246,plain,
    ( spl43_154
  <=> sK4 = k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,sK4),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_154])])).

fof(f8907,plain,
    ( sK4 != k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,sK4),k2_struct_0(sK3))
    | ~ spl43_9
    | ~ spl43_134
    | ~ spl43_294 ),
    inference(subsumption_resolution,[],[f8877,f6645])).

fof(f6645,plain,
    ( m1_subset_1(sK15(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl43_134 ),
    inference(avatar_component_clause,[],[f6643])).

fof(f6643,plain,
    ( spl43_134
  <=> m1_subset_1(sK15(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_134])])).

fof(f8877,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 != k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,sK4),k2_struct_0(sK3))
    | ~ spl43_9
    | ~ spl43_294 ),
    inference(resolution,[],[f8471,f3256])).

fof(f3256,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != sK4 )
    | ~ spl43_9 ),
    inference(avatar_component_clause,[],[f3255])).

fof(f3255,plain,
    ( spl43_9
  <=> ! [X3] :
        ( k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != sK4
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_9])])).

fof(f8471,plain,
    ( v3_pre_topc(sK15(sK2,sK3,sK4),sK2)
    | ~ spl43_294 ),
    inference(avatar_component_clause,[],[f8469])).

fof(f8469,plain,
    ( spl43_294
  <=> v3_pre_topc(sK15(sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_294])])).

fof(f8472,plain,
    ( spl43_294
    | ~ spl43_1
    | ~ spl43_121
    | ~ spl43_134 ),
    inference(avatar_split_clause,[],[f6880,f6643,f6552,f2913,f8469])).

fof(f6552,plain,
    ( spl43_121
  <=> r2_hidden(sK15(sK2,sK3,sK4),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_121])])).

fof(f6880,plain,
    ( v3_pre_topc(sK15(sK2,sK3,sK4),sK2)
    | ~ spl43_1
    | ~ spl43_121
    | ~ spl43_134 ),
    inference(subsumption_resolution,[],[f6879,f2915])).

fof(f6879,plain,
    ( v3_pre_topc(sK15(sK2,sK3,sK4),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl43_121
    | ~ spl43_134 ),
    inference(subsumption_resolution,[],[f6836,f6554])).

fof(f6554,plain,
    ( r2_hidden(sK15(sK2,sK3,sK4),u1_pre_topc(sK2))
    | ~ spl43_121 ),
    inference(avatar_component_clause,[],[f6552])).

fof(f6836,plain,
    ( ~ r2_hidden(sK15(sK2,sK3,sK4),u1_pre_topc(sK2))
    | v3_pre_topc(sK15(sK2,sK3,sK4),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl43_134 ),
    inference(resolution,[],[f6645,f2849])).

fof(f2849,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2643])).

fof(f2643,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2501])).

fof(f2501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1774])).

fof(f1774,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f7249,plain,
    ( spl43_154
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10
    | ~ spl43_20 ),
    inference(avatar_split_clause,[],[f5994,f3321,f3259,f2963,f2926,f2913,f7246])).

fof(f3259,plain,
    ( spl43_10
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_10])])).

fof(f5994,plain,
    ( sK4 = k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,sK4),k2_struct_0(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10
    | ~ spl43_20 ),
    inference(subsumption_resolution,[],[f5992,f3323])).

fof(f3323,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl43_20 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f5992,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | sK4 = k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,sK4),k2_struct_0(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10 ),
    inference(resolution,[],[f4911,f2965])).

fof(f4911,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X2,u1_pre_topc(sK3))
        | k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,X2),k2_struct_0(sK3)) = X2 )
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_10 ),
    inference(subsumption_resolution,[],[f2947,f3261])).

fof(f3261,plain,
    ( l1_pre_topc(sK3)
    | ~ spl43_10 ),
    inference(avatar_component_clause,[],[f3259])).

fof(f2947,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_pre_topc(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,X2),k2_struct_0(sK3)) = X2
        | ~ l1_pre_topc(sK3) )
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(subsumption_resolution,[],[f2933,f2915])).

fof(f2933,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_pre_topc(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | k9_subset_1(u1_struct_0(sK3),sK15(sK2,sK3,X2),k2_struct_0(sK3)) = X2
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK2) )
    | ~ spl43_2 ),
    inference(resolution,[],[f2928,f2723])).

fof(f2723,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),sK15(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2589])).

fof(f6646,plain,
    ( spl43_134
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10
    | ~ spl43_20 ),
    inference(avatar_split_clause,[],[f5979,f3321,f3259,f2963,f2926,f2913,f6643])).

fof(f5979,plain,
    ( m1_subset_1(sK15(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10
    | ~ spl43_20 ),
    inference(subsumption_resolution,[],[f5977,f3323])).

fof(f5977,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | m1_subset_1(sK15(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10 ),
    inference(resolution,[],[f4913,f2965])).

fof(f4913,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_pre_topc(sK3))
        | m1_subset_1(sK15(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_10 ),
    inference(subsumption_resolution,[],[f2945,f3261])).

fof(f2945,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | m1_subset_1(sK15(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK3) )
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(subsumption_resolution,[],[f2931,f2915])).

fof(f2931,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | m1_subset_1(sK15(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK2) )
    | ~ spl43_2 ),
    inference(resolution,[],[f2928,f2721])).

fof(f2721,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK15(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2589])).

fof(f6555,plain,
    ( spl43_121
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10
    | ~ spl43_20 ),
    inference(avatar_split_clause,[],[f5937,f3321,f3259,f2963,f2926,f2913,f6552])).

fof(f5937,plain,
    ( r2_hidden(sK15(sK2,sK3,sK4),u1_pre_topc(sK2))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10
    | ~ spl43_20 ),
    inference(subsumption_resolution,[],[f5935,f3323])).

fof(f5935,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | r2_hidden(sK15(sK2,sK3,sK4),u1_pre_topc(sK2))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_10 ),
    inference(resolution,[],[f4912,f2965])).

fof(f4912,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X1,u1_pre_topc(sK3))
        | r2_hidden(sK15(sK2,sK3,X1),u1_pre_topc(sK2)) )
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_10 ),
    inference(subsumption_resolution,[],[f2946,f3261])).

fof(f2946,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | r2_hidden(sK15(sK2,sK3,X1),u1_pre_topc(sK2))
        | ~ l1_pre_topc(sK3) )
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(subsumption_resolution,[],[f2932,f2915])).

fof(f2932,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | r2_hidden(sK15(sK2,sK3,X1),u1_pre_topc(sK2))
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK2) )
    | ~ spl43_2 ),
    inference(resolution,[],[f2928,f2722])).

fof(f2722,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK15(X0,X1,X5),u1_pre_topc(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2589])).

fof(f5774,plain,
    ( spl43_4
    | ~ spl43_20
    | ~ spl43_3
    | ~ spl43_10 ),
    inference(avatar_split_clause,[],[f5641,f3259,f2963,f3321,f3079])).

fof(f3079,plain,
    ( spl43_4
  <=> v3_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_4])])).

fof(f5641,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | v3_pre_topc(sK4,sK3)
    | ~ spl43_3
    | ~ spl43_10 ),
    inference(subsumption_resolution,[],[f4948,f3261])).

fof(f4948,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | v3_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl43_3 ),
    inference(resolution,[],[f2965,f2849])).

fof(f4144,plain,
    ( ~ spl43_7
    | spl43_48
    | ~ spl43_1
    | ~ spl43_5 ),
    inference(avatar_split_clause,[],[f3150,f3083,f2913,f4141,f3153])).

fof(f3083,plain,
    ( spl43_5
  <=> v3_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_5])])).

fof(f3150,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl43_1
    | ~ spl43_5 ),
    inference(subsumption_resolution,[],[f3118,f2915])).

fof(f3118,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl43_5 ),
    inference(resolution,[],[f3085,f2848])).

fof(f2848,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2643])).

fof(f3085,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ spl43_5 ),
    inference(avatar_component_clause,[],[f3083])).

fof(f3324,plain,
    ( spl43_20
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_4 ),
    inference(avatar_split_clause,[],[f3246,f3079,f2963,f2926,f2913,f3321])).

fof(f3246,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl43_1
    | ~ spl43_2
    | ~ spl43_3
    | ~ spl43_4 ),
    inference(subsumption_resolution,[],[f3245,f2952])).

fof(f3245,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ spl43_3
    | ~ spl43_4 ),
    inference(subsumption_resolution,[],[f3183,f2965])).

fof(f3183,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ spl43_4 ),
    inference(resolution,[],[f3081,f2848])).

fof(f3081,plain,
    ( v3_pre_topc(sK4,sK3)
    | ~ spl43_4 ),
    inference(avatar_component_clause,[],[f3079])).

fof(f3262,plain,
    ( spl43_10
    | ~ spl43_1
    | ~ spl43_2 ),
    inference(avatar_split_clause,[],[f2952,f2926,f2913,f3259])).

fof(f3257,plain,
    ( ~ spl43_4
    | spl43_9 ),
    inference(avatar_split_clause,[],[f2672,f3255,f3079])).

fof(f2672,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != sK4
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f2555])).

fof(f2555,plain,
    ( ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != sK4
          | ~ v3_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v3_pre_topc(sK4,sK3) )
    & ( ( sK4 = k9_subset_1(u1_struct_0(sK3),sK5,k2_struct_0(sK3))
        & v3_pre_topc(sK5,sK2)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v3_pre_topc(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f2550,f2554,f2553,f2552,f2551])).

fof(f2551,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v3_pre_topc(X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,sK2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,sK2)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2552,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              | ~ v3_pre_topc(X2,X1) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                  & v3_pre_topc(X4,sK2)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
              | v3_pre_topc(X2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X1,sK2) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != X2
                | ~ v3_pre_topc(X3,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | ~ v3_pre_topc(X2,sK3) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(sK3),X4,k2_struct_0(sK3)) = X2
                & v3_pre_topc(X4,sK2)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
            | v3_pre_topc(X2,sK3) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_pre_topc(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2553,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != X2
              | ~ v3_pre_topc(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ v3_pre_topc(X2,sK3) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(sK3),X4,k2_struct_0(sK3)) = X2
              & v3_pre_topc(X4,sK2)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
          | v3_pre_topc(X2,sK3) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ( ! [X3] :
            ( k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)) != sK4
            | ~ v3_pre_topc(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        | ~ v3_pre_topc(sK4,sK3) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(sK3),X4,k2_struct_0(sK3)) = sK4
            & v3_pre_topc(X4,sK2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
        | v3_pre_topc(sK4,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f2554,plain,
    ( ? [X4] :
        ( k9_subset_1(u1_struct_0(sK3),X4,k2_struct_0(sK3)) = sK4
        & v3_pre_topc(X4,sK2)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( sK4 = k9_subset_1(u1_struct_0(sK3),sK5,k2_struct_0(sK3))
      & v3_pre_topc(sK5,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2550,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2549])).

fof(f2549,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2548])).

fof(f2548,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2379])).

fof(f2379,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,X1)
              <~> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2367])).

fof(f2367,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X2,X1)
                <=> ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2366])).

fof(f2366,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f3253,plain,
    ( spl43_4
    | spl43_8 ),
    inference(avatar_split_clause,[],[f2671,f3250,f3079])).

fof(f2671,plain,
    ( sK4 = k9_subset_1(u1_struct_0(sK3),sK5,k2_struct_0(sK3))
    | v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f2555])).

fof(f3156,plain,
    ( spl43_4
    | spl43_7 ),
    inference(avatar_split_clause,[],[f2669,f3153,f3079])).

fof(f2669,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f2555])).

fof(f3086,plain,
    ( spl43_4
    | spl43_5 ),
    inference(avatar_split_clause,[],[f2670,f3083,f3079])).

fof(f2670,plain,
    ( v3_pre_topc(sK5,sK2)
    | v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f2555])).

fof(f2966,plain,(
    spl43_3 ),
    inference(avatar_split_clause,[],[f2668,f2963])).

fof(f2668,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f2555])).

fof(f2929,plain,(
    spl43_2 ),
    inference(avatar_split_clause,[],[f2667,f2926])).

fof(f2667,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f2555])).

fof(f2916,plain,(
    spl43_1 ),
    inference(avatar_split_clause,[],[f2666,f2913])).

fof(f2666,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2555])).
%------------------------------------------------------------------------------
