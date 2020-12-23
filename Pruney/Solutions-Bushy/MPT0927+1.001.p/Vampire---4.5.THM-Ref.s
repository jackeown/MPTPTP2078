%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0927+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:54 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  275 ( 853 expanded)
%              Number of leaves         :   62 ( 379 expanded)
%              Depth                    :   11
%              Number of atoms          :  946 (4541 expanded)
%              Number of equality atoms :  317 ( 785 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f179,f204,f219,f227,f267,f297,f308,f326,f391,f403,f415,f425,f471,f475,f487,f498,f501,f513,f524,f552,f555,f567,f583,f584,f585,f586,f588,f594,f617,f636,f652,f674,f679,f688,f689,f690,f697,f702,f705,f710,f713])).

fof(f713,plain,
    ( ~ spl10_43
    | spl10_48
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f711,f670,f708,f649])).

fof(f649,plain,
    ( spl10_43
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f708,plain,
    ( spl10_48
  <=> m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f670,plain,
    ( spl10_45
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f711,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_45 ),
    inference(superposition,[],[f63,f671])).

fof(f671,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f670])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f710,plain,
    ( ~ spl10_48
    | spl10_31
    | spl10_4 ),
    inference(avatar_split_clause,[],[f706,f96,f344,f708])).

fof(f344,plain,
    ( spl10_31
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f96,plain,
    ( spl10_4
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f706,plain,
    ( v1_xboole_0(sK7)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_4 ),
    inference(resolution,[],[f97,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f97,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f705,plain,
    ( ~ spl10_43
    | spl10_47
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f703,f660,f700,f649])).

fof(f700,plain,
    ( spl10_47
  <=> m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f660,plain,
    ( spl10_44
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f703,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_44 ),
    inference(superposition,[],[f62,f661])).

fof(f661,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f660])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f702,plain,
    ( ~ spl10_47
    | spl10_25
    | spl10_3 ),
    inference(avatar_split_clause,[],[f698,f93,f234,f700])).

fof(f234,plain,
    ( spl10_25
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f93,plain,
    ( spl10_3
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f698,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_3 ),
    inference(resolution,[],[f94,f52])).

fof(f94,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f697,plain,
    ( ~ spl10_43
    | spl10_46
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f695,f644,f677,f649])).

fof(f677,plain,
    ( spl10_46
  <=> m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f644,plain,
    ( spl10_42
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f695,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_42 ),
    inference(superposition,[],[f60,f645])).

fof(f645,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f644])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f690,plain,
    ( spl10_42
    | spl10_35
    | spl10_34
    | spl10_33
    | spl10_32
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f682,f152,f352,f355,f358,f361,f644])).

fof(f361,plain,
    ( spl10_35
  <=> o_0_0_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f358,plain,
    ( spl10_34
  <=> o_0_0_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f355,plain,
    ( spl10_33
  <=> o_0_0_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f352,plain,
    ( spl10_32
  <=> o_0_0_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f152,plain,
    ( spl10_18
  <=> ! [X5,X7,X4,X6] :
        ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(X4,X5,X6,X7,sK8)
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f682,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_18 ),
    inference(resolution,[],[f164,f153])).

fof(f153,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X4,X5,X6,X7))
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5
        | o_0_0_xboole_0 = X6
        | o_0_0_xboole_0 = X7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(X4,X5,X6,X7,sK8) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f164,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f45,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f18,f34,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                    & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
            & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                  & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
              & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                  | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                  | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
            & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
                | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
              & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
          & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
              | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
              | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
              | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
            & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
            & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
        & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
   => ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
            | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
            | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
            | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
          & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X8] :
        ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
          | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
          | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
          | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
        & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
      & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f689,plain,
    ( spl10_44
    | spl10_35
    | spl10_34
    | spl10_33
    | spl10_32
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f681,f156,f352,f355,f358,f361,f660])).

fof(f156,plain,
    ( spl10_19
  <=> ! [X9,X11,X8,X10] :
        ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(X8,X9,X10,X11,sK8)
        | o_0_0_xboole_0 = X8
        | o_0_0_xboole_0 = X9
        | o_0_0_xboole_0 = X10
        | o_0_0_xboole_0 = X11
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X8,X9,X10,X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f681,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_19 ),
    inference(resolution,[],[f164,f157])).

fof(f157,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X8,X9,X10,X11))
        | o_0_0_xboole_0 = X8
        | o_0_0_xboole_0 = X9
        | o_0_0_xboole_0 = X10
        | o_0_0_xboole_0 = X11
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(X8,X9,X10,X11,sK8) )
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f688,plain,
    ( spl10_45
    | spl10_35
    | spl10_34
    | spl10_33
    | spl10_32
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f680,f160,f352,f355,f358,f361,f670])).

fof(f160,plain,
    ( spl10_20
  <=> ! [X13,X15,X12,X14] :
        ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(X12,X13,X14,X15,sK8)
        | o_0_0_xboole_0 = X12
        | o_0_0_xboole_0 = X13
        | o_0_0_xboole_0 = X14
        | o_0_0_xboole_0 = X15
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X12,X13,X14,X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f680,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_20 ),
    inference(resolution,[],[f164,f161])).

fof(f161,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X12,X13,X14,X15))
        | o_0_0_xboole_0 = X12
        | o_0_0_xboole_0 = X13
        | o_0_0_xboole_0 = X14
        | o_0_0_xboole_0 = X15
        | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(X12,X13,X14,X15,sK8) )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f679,plain,
    ( ~ spl10_46
    | spl10_28
    | spl10_2 ),
    inference(avatar_split_clause,[],[f675,f90,f286,f677])).

fof(f286,plain,
    ( spl10_28
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f90,plain,
    ( spl10_2
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f675,plain,
    ( v1_xboole_0(sK5)
    | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_2 ),
    inference(resolution,[],[f91,f52])).

fof(f91,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f674,plain,(
    spl10_43 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | spl10_43 ),
    inference(subsumption_resolution,[],[f164,f650])).

fof(f650,plain,
    ( ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | spl10_43 ),
    inference(avatar_component_clause,[],[f649])).

fof(f652,plain,
    ( ~ spl10_43
    | spl10_21
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f647,f445,f167,f649])).

fof(f167,plain,
    ( spl10_21
  <=> m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f445,plain,
    ( spl10_40
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f647,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_40 ),
    inference(superposition,[],[f61,f446])).

fof(f446,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f445])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f636,plain,
    ( spl10_40
    | spl10_35
    | spl10_34
    | spl10_33
    | spl10_32
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f631,f148,f352,f355,f358,f361,f445])).

fof(f148,plain,
    ( spl10_17
  <=> ! [X1,X3,X0,X2] :
        ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(X0,X1,X2,X3,sK8)
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 = X3
        | ~ m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f631,plain,
    ( o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_17 ),
    inference(resolution,[],[f149,f164])).

fof(f149,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3))
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 = X3
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(X0,X1,X2,X3,sK8) )
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f617,plain,(
    ~ spl10_31 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f47,f611])).

fof(f611,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_31 ),
    inference(forward_demodulation,[],[f606,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X3
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f59,f48,f48])).

fof(f48,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f606,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,o_0_0_xboole_0))
    | ~ spl10_31 ),
    inference(backward_demodulation,[],[f163,f595])).

fof(f595,plain,
    ( o_0_0_xboole_0 = sK7
    | ~ spl10_31 ),
    inference(resolution,[],[f345,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f345,plain,
    ( v1_xboole_0(sK7)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f344])).

fof(f163,plain,(
    ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f594,plain,(
    ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl10_30 ),
    inference(resolution,[],[f342,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f7,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f342,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK7)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl10_30
  <=> ! [X0] : ~ m1_subset_1(X0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f588,plain,
    ( ~ spl10_21
    | spl10_22
    | spl10_1 ),
    inference(avatar_split_clause,[],[f587,f87,f170,f167])).

fof(f170,plain,
    ( spl10_22
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f87,plain,
    ( spl10_1
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f587,plain,
    ( v1_xboole_0(sK4)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_1 ),
    inference(resolution,[],[f88,f52])).

fof(f88,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f586,plain,
    ( spl10_13
    | spl10_14
    | spl10_15
    | spl10_16
    | spl10_20 ),
    inference(avatar_split_clause,[],[f582,f160,f145,f142,f139,f136])).

fof(f136,plain,
    ( spl10_13
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f139,plain,
    ( spl10_14
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f142,plain,
    ( spl10_15
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f145,plain,
    ( spl10_16
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f582,plain,(
    ! [X14,X12,X15,X13] :
      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(X12,X13,X14,X15,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X12,X13,X14,X15))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X15
      | o_0_0_xboole_0 = X14
      | o_0_0_xboole_0 = X13
      | o_0_0_xboole_0 = X12 ) ),
    inference(resolution,[],[f44,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k11_mcart_1(X4,X5,X6,X7,X9) = k11_mcart_1(X0,X1,X2,X3,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f48,f48,f48,f48,f48,f48,f48,f48])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ! [X8] :
          ( ! [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
              | X8 != X9
              | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ~ ( ? [X8] :
            ( ? [X9] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                    & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                    & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                    & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

fof(f44,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f585,plain,
    ( spl10_13
    | spl10_14
    | spl10_15
    | spl10_16
    | spl10_19 ),
    inference(avatar_split_clause,[],[f581,f156,f145,f142,f139,f136])).

fof(f581,plain,(
    ! [X10,X8,X11,X9] :
      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(X8,X9,X10,X11,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X8,X9,X10,X11))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X11
      | o_0_0_xboole_0 = X10
      | o_0_0_xboole_0 = X9
      | o_0_0_xboole_0 = X8 ) ),
    inference(resolution,[],[f44,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k10_mcart_1(X4,X5,X6,X7,X9) = k10_mcart_1(X0,X1,X2,X3,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f66,f48,f48,f48,f48,f48,f48,f48,f48])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f584,plain,
    ( spl10_13
    | spl10_14
    | spl10_15
    | spl10_16
    | spl10_18 ),
    inference(avatar_split_clause,[],[f580,f152,f145,f142,f139,f136])).

fof(f580,plain,(
    ! [X6,X4,X7,X5] :
      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(X4,X5,X6,X7,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X4,X5,X6,X7))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4 ) ),
    inference(resolution,[],[f44,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k9_mcart_1(X4,X5,X6,X7,X9) = k9_mcart_1(X0,X1,X2,X3,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f48,f48,f48,f48,f48,f48,f48,f48])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f583,plain,
    ( spl10_13
    | spl10_14
    | spl10_15
    | spl10_16
    | spl10_17 ),
    inference(avatar_split_clause,[],[f579,f148,f145,f142,f139,f136])).

fof(f579,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(X0,X1,X2,X3,sK8)
      | ~ m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = sK3
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f44,f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | k8_mcart_1(X4,X5,X6,X7,X9) = k8_mcart_1(X0,X1,X2,X3,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f48,f48,f48,f48,f48,f48,f48,f48])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f567,plain,
    ( spl10_30
    | spl10_31
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f566,f125,f344,f341])).

fof(f125,plain,
    ( spl10_11
  <=> ! [X0] : ~ r2_hidden(X0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f566,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK7)
        | ~ m1_subset_1(X0,sK7) )
    | ~ spl10_11 ),
    inference(resolution,[],[f126,f52])).

fof(f126,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK7)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f555,plain,
    ( spl10_7
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f554,f112,f109])).

fof(f109,plain,
    ( spl10_7
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f112,plain,
    ( spl10_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f554,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f552,plain,(
    ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f47,f546])).

fof(f546,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_28 ),
    inference(forward_demodulation,[],[f543,f80])).

fof(f80,plain,(
    ! [X2,X0,X3] : o_0_0_xboole_0 = k4_zfmisc_1(X0,o_0_0_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f57,f48,f48])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f543,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(sK4,o_0_0_xboole_0,sK6,sK7))
    | ~ spl10_28 ),
    inference(backward_demodulation,[],[f163,f530])).

fof(f530,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl10_28 ),
    inference(resolution,[],[f287,f68])).

fof(f287,plain,
    ( v1_xboole_0(sK5)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f286])).

% (20885)Refutation not found, incomplete strategy% (20885)------------------------------
% (20885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f524,plain,(
    ~ spl10_27 ),
    inference(avatar_contradiction_clause,[],[f523])).

% (20885)Termination reason: Refutation not found, incomplete strategy

% (20885)Memory used [KB]: 10874
% (20885)Time elapsed: 0.182 s
% (20885)------------------------------
% (20885)------------------------------
fof(f523,plain,
    ( $false
    | ~ spl10_27 ),
    inference(resolution,[],[f284,f50])).

fof(f284,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK5)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl10_27
  <=> ! [X0] : ~ m1_subset_1(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f513,plain,
    ( spl10_27
    | spl10_28
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f512,f109,f286,f283])).

fof(f512,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK5)
        | ~ m1_subset_1(X0,sK5) )
    | ~ spl10_7 ),
    inference(resolution,[],[f110,f52])).

fof(f110,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f501,plain,
    ( spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f500,f104,f101])).

fof(f101,plain,
    ( spl10_5
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f104,plain,
    ( spl10_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f500,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f40,f54])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f498,plain,(
    ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl10_26 ),
    inference(resolution,[],[f252,f50])).

fof(f252,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl10_26
  <=> ! [X0] : ~ m1_subset_1(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f487,plain,
    ( spl10_26
    | spl10_22
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f486,f101,f170,f251])).

fof(f486,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4)
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl10_5 ),
    inference(resolution,[],[f102,f52])).

fof(f102,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f475,plain,
    ( spl10_9
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f474,f120,f117])).

fof(f117,plain,
    ( spl10_9
  <=> ! [X0] : ~ r2_hidden(X0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f120,plain,
    ( spl10_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f474,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f42,f54])).

fof(f42,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f471,plain,(
    ~ spl10_25 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f47,f465])).

fof(f465,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_25 ),
    inference(forward_demodulation,[],[f462,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] : o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,o_0_0_xboole_0,X3) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f58,f48,f48])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f462,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,o_0_0_xboole_0,sK7))
    | ~ spl10_25 ),
    inference(backward_demodulation,[],[f163,f449])).

fof(f449,plain,
    ( o_0_0_xboole_0 = sK6
    | ~ spl10_25 ),
    inference(resolution,[],[f235,f68])).

fof(f235,plain,
    ( v1_xboole_0(sK6)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f234])).

fof(f425,plain,(
    ~ spl10_35 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f47,f422])).

fof(f422,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_35 ),
    inference(resolution,[],[f421,f53])).

fof(f421,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_35 ),
    inference(forward_demodulation,[],[f420,f78])).

fof(f420,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,o_0_0_xboole_0))
    | ~ spl10_35 ),
    inference(forward_demodulation,[],[f45,f362])).

fof(f362,plain,
    ( o_0_0_xboole_0 = sK7
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f361])).

fof(f415,plain,(
    ~ spl10_34 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f47,f411])).

fof(f411,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_34 ),
    inference(resolution,[],[f410,f53])).

fof(f410,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f408,f79])).

fof(f408,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,o_0_0_xboole_0,sK7))
    | ~ spl10_34 ),
    inference(backward_demodulation,[],[f45,f359])).

fof(f359,plain,
    ( o_0_0_xboole_0 = sK6
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f358])).

fof(f403,plain,(
    ~ spl10_33 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f47,f398])).

fof(f398,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_33 ),
    inference(resolution,[],[f397,f53])).

fof(f397,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f396,f80])).

fof(f396,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(sK4,o_0_0_xboole_0,sK6,sK7))
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f45,f356])).

fof(f356,plain,
    ( o_0_0_xboole_0 = sK5
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f355])).

fof(f391,plain,(
    ~ spl10_32 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f47,f385])).

fof(f385,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_32 ),
    inference(forward_demodulation,[],[f380,f81])).

fof(f81,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k4_zfmisc_1(o_0_0_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f56,f48,f48])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f380,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1(o_0_0_xboole_0,sK5,sK6,sK7))
    | ~ spl10_32 ),
    inference(backward_demodulation,[],[f163,f353])).

fof(f353,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f352])).

fof(f326,plain,(
    ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl10_24 ),
    inference(resolution,[],[f232,f50])).

fof(f232,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK6)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl10_24
  <=> ! [X0] : ~ m1_subset_1(X0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f308,plain,
    ( spl10_24
    | spl10_25
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f307,f117,f234,f231])).

fof(f307,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK6)
        | ~ m1_subset_1(X0,sK6) )
    | ~ spl10_9 ),
    inference(resolution,[],[f118,f52])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f297,plain,
    ( spl10_11
    | ~ spl10_23
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f296,f145,f200,f125])).

fof(f200,plain,
    ( spl10_23
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl10_16 ),
    inference(resolution,[],[f294,f54])).

fof(f294,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl10_16 ),
    inference(backward_demodulation,[],[f43,f146])).

fof(f146,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f43,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f267,plain,(
    ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f47,f263])).

fof(f263,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_22 ),
    inference(resolution,[],[f262,f53])).

fof(f262,plain,
    ( r2_hidden(sK8,o_0_0_xboole_0)
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f261,f81])).

fof(f261,plain,
    ( r2_hidden(sK8,k4_zfmisc_1(o_0_0_xboole_0,sK5,sK6,sK7))
    | ~ spl10_22 ),
    inference(backward_demodulation,[],[f45,f254])).

fof(f254,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl10_22 ),
    inference(resolution,[],[f171,f68])).

fof(f171,plain,
    ( v1_xboole_0(sK4)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f227,plain,
    ( spl10_10
    | ~ spl10_15 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl10_10
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f47,f223])).

fof(f223,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl10_10
    | ~ spl10_15 ),
    inference(backward_demodulation,[],[f121,f143])).

fof(f143,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f219,plain,(
    spl10_23 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl10_23 ),
    inference(subsumption_resolution,[],[f47,f201])).

fof(f201,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl10_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f204,plain,
    ( spl10_8
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl10_8
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f47,f195])).

fof(f195,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl10_8
    | ~ spl10_14 ),
    inference(backward_demodulation,[],[f113,f140])).

fof(f140,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f179,plain,
    ( spl10_6
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl10_6
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f47,f175])).

fof(f175,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl10_6
    | ~ spl10_13 ),
    inference(backward_demodulation,[],[f105,f137])).

fof(f137,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f98,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f46,f96,f93,f90,f87])).

fof(f46,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
