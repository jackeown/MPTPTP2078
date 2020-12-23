%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:51 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  223 (1059 expanded)
%              Number of leaves         :   40 ( 368 expanded)
%              Depth                    :   13
%              Number of atoms          :  742 (5665 expanded)
%              Number of equality atoms :  219 ( 980 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f237,f506,f524,f606,f622,f638,f682,f824,f929,f981,f1072,f1121,f1202,f1220,f1229,f1237,f1242,f1246])).

fof(f1246,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | spl10_4
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f1245,f504,f98,f232,f229,f226,f223])).

fof(f223,plain,
    ( spl10_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f226,plain,
    ( spl10_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f229,plain,
    ( spl10_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f232,plain,
    ( spl10_18
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f98,plain,
    ( spl10_4
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f504,plain,
    ( spl10_31
  <=> m1_subset_1(k2_mcart_1(sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f1245,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_4
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f1244,f51])).

fof(f51,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f36,f35,f34,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f1244,plain,
    ( ~ m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_4
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f1243,f789])).

fof(f789,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f787,f271])).

fof(f271,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(superposition,[],[f104,f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X1,X2,X3,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f84,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f104,plain,(
    ~ v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f787,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | v1_xboole_0(sK7)
    | ~ spl10_31 ),
    inference(resolution,[],[f505,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f505,plain,
    ( m1_subset_1(k2_mcart_1(sK8),sK7)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1243,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_4 ),
    inference(superposition,[],[f99,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f99,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1242,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | spl10_3
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f1241,f822,f95,f232,f229,f226,f223])).

fof(f95,plain,
    ( spl10_3
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f822,plain,
    ( spl10_46
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f1241,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_3
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f1240,f51])).

fof(f1240,plain,
    ( ~ m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_3
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f1239,f1212])).

fof(f1212,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f1210,f294])).

fof(f294,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(superposition,[],[f104,f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X1,X2,X0,X3) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f85,f55])).

fof(f85,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1210,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | v1_xboole_0(sK6)
    | ~ spl10_46 ),
    inference(resolution,[],[f823,f58])).

fof(f823,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f822])).

fof(f1239,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_3 ),
    inference(superposition,[],[f96,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1237,plain,
    ( ~ spl10_57
    | spl10_58 ),
    inference(avatar_contradiction_clause,[],[f1236])).

fof(f1236,plain,
    ( $false
    | ~ spl10_57
    | spl10_58 ),
    inference(subsumption_resolution,[],[f1235,f319])).

fof(f319,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(superposition,[],[f104,f158])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X1,X0,X2,X3) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f86,f55])).

fof(f86,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1235,plain,
    ( v1_xboole_0(sK5)
    | ~ spl10_57
    | spl10_58 ),
    inference(subsumption_resolution,[],[f1233,f1228])).

fof(f1228,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | spl10_58 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1227,plain,
    ( spl10_58
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f1233,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | v1_xboole_0(sK5)
    | ~ spl10_57 ),
    inference(resolution,[],[f1201,f58])).

fof(f1201,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1200,plain,
    ( spl10_57
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f1229,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_58
    | spl10_2 ),
    inference(avatar_split_clause,[],[f1225,f92,f1227,f232,f229,f226,f223])).

fof(f92,plain,
    ( spl10_2
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1225,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_2 ),
    inference(subsumption_resolution,[],[f1224,f51])).

fof(f1224,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_2 ),
    inference(superposition,[],[f93,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1220,plain,
    ( spl10_19
    | ~ spl10_55 ),
    inference(avatar_contradiction_clause,[],[f1219])).

fof(f1219,plain,
    ( $false
    | spl10_19
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f1218,f346])).

fof(f346,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(superposition,[],[f104,f159])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f87,f55])).

fof(f87,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1218,plain,
    ( v1_xboole_0(sK4)
    | spl10_19
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f1216,f236])).

fof(f236,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl10_19
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f1216,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | v1_xboole_0(sK4)
    | ~ spl10_55 ),
    inference(resolution,[],[f1071,f58])).

fof(f1071,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl10_55
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f1202,plain,
    ( spl10_27
    | spl10_28
    | spl10_29
    | spl10_30
    | spl10_57 ),
    inference(avatar_split_clause,[],[f1180,f1200,f501,f498,f495,f492])).

fof(f492,plain,
    ( spl10_27
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f495,plain,
    ( spl10_28
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f498,plain,
    ( spl10_29
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f501,plain,
    ( spl10_30
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f1180,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f239,f106])).

fof(f106,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(resolution,[],[f101,f52])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f59,f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f239,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f82,f76])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f1121,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1106,f244])).

fof(f244,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f187,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f187,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f183,f182])).

fof(f182,plain,(
    ! [X4] : k1_xboole_0 != k1_tarski(X4) ),
    inference(subsumption_resolution,[],[f181,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tarski(X0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f181,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_tarski(X4)
      | r2_hidden(X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_tarski(X4)
      | r2_hidden(X4,X5)
      | r2_hidden(X4,X5) ) ),
    inference(superposition,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f183,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_tarski(X2)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f83,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f83,plain,(
    ! [X2,X1] :
      ( k1_tarski(X2) = k3_xboole_0(k2_tarski(X2,X2),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f1106,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f271,f1101])).

fof(f1101,plain,
    ( k1_xboole_0 = sK7
    | ~ spl10_18 ),
    inference(resolution,[],[f1079,f172])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f62,f54])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1079,plain,
    ( r1_tarski(sK7,k1_xboole_0)
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f154,f233])).

fof(f233,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f154,plain,(
    r1_tarski(sK7,sK3) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1072,plain,
    ( spl10_27
    | spl10_28
    | spl10_29
    | spl10_30
    | spl10_55 ),
    inference(avatar_split_clause,[],[f1050,f1070,f501,f498,f495,f492])).

fof(f1050,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f220,f106])).

fof(f220,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f81,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f981,plain,(
    ~ spl10_17 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f967,f244])).

fof(f967,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_17 ),
    inference(backward_demodulation,[],[f294,f962])).

fof(f962,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_17 ),
    inference(resolution,[],[f935,f172])).

fof(f935,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | ~ spl10_17 ),
    inference(backward_demodulation,[],[f153,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f229])).

fof(f153,plain,(
    r1_tarski(sK6,sK2) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f929,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f916,f244])).

fof(f916,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_16 ),
    inference(backward_demodulation,[],[f319,f911])).

fof(f911,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_16 ),
    inference(resolution,[],[f888,f172])).

fof(f888,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl10_16 ),
    inference(backward_demodulation,[],[f152,f227])).

fof(f227,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f152,plain,(
    r1_tarski(sK5,sK1) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f824,plain,
    ( spl10_27
    | spl10_28
    | spl10_29
    | spl10_30
    | spl10_46 ),
    inference(avatar_split_clause,[],[f802,f822,f501,f498,f495,f492])).

fof(f802,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f215,f106])).

fof(f215,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f79,f77])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f682,plain,(
    ~ spl10_15 ),
    inference(avatar_contradiction_clause,[],[f681])).

fof(f681,plain,
    ( $false
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f667,f244])).

fof(f667,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_15 ),
    inference(backward_demodulation,[],[f346,f661])).

fof(f661,plain,
    ( k1_xboole_0 = sK4
    | ~ spl10_15 ),
    inference(resolution,[],[f588,f172])).

fof(f588,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl10_15 ),
    inference(forward_demodulation,[],[f151,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f223])).

fof(f151,plain,(
    r1_tarski(sK4,sK0) ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f638,plain,(
    ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f629,f244])).

fof(f629,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f271,f502])).

fof(f502,plain,
    ( k1_xboole_0 = sK7
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f501])).

fof(f622,plain,(
    ~ spl10_29 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f613,f244])).

fof(f613,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_29 ),
    inference(backward_demodulation,[],[f294,f499])).

fof(f499,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f498])).

fof(f606,plain,(
    ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f597,f244])).

fof(f597,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_28 ),
    inference(backward_demodulation,[],[f319,f496])).

fof(f496,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f495])).

fof(f524,plain,(
    ~ spl10_27 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f515,f244])).

fof(f515,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_27 ),
    inference(backward_demodulation,[],[f346,f493])).

fof(f493,plain,
    ( k1_xboole_0 = sK4
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f492])).

fof(f506,plain,
    ( spl10_27
    | spl10_28
    | spl10_29
    | spl10_30
    | spl10_31 ),
    inference(avatar_split_clause,[],[f472,f504,f501,f498,f495,f492])).

fof(f472,plain,
    ( m1_subset_1(k2_mcart_1(sK8),sK7)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f213,f106])).

fof(f213,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k2_mcart_1(X4),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f80,f78])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f237,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_19
    | spl10_1 ),
    inference(avatar_split_clause,[],[f221,f89,f235,f232,f229,f226,f223])).

fof(f89,plain,
    ( spl10_1
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f221,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_1 ),
    inference(subsumption_resolution,[],[f218,f51])).

fof(f218,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_1 ),
    inference(superposition,[],[f90,f75])).

fof(f90,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f100,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f53,f98,f95,f92,f89])).

fof(f53,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (6361)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (6358)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (6347)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (6349)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (6357)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (6357)Refutation not found, incomplete strategy% (6357)------------------------------
% 0.22/0.50  % (6357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6357)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (6357)Memory used [KB]: 6140
% 0.22/0.50  % (6357)Time elapsed: 0.077 s
% 0.22/0.50  % (6357)------------------------------
% 0.22/0.50  % (6357)------------------------------
% 0.22/0.50  % (6347)Refutation not found, incomplete strategy% (6347)------------------------------
% 0.22/0.50  % (6347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6347)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (6347)Memory used [KB]: 6652
% 0.22/0.50  % (6347)Time elapsed: 0.068 s
% 0.22/0.50  % (6347)------------------------------
% 0.22/0.50  % (6347)------------------------------
% 0.22/0.50  % (6360)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (6366)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (6350)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (6363)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (6359)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (6353)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (6362)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (6364)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (6348)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (6348)Refutation not found, incomplete strategy% (6348)------------------------------
% 0.22/0.52  % (6348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6348)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6348)Memory used [KB]: 10618
% 0.22/0.52  % (6348)Time elapsed: 0.096 s
% 0.22/0.52  % (6348)------------------------------
% 0.22/0.52  % (6348)------------------------------
% 0.22/0.52  % (6355)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (6354)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (6352)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (6367)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (6367)Refutation not found, incomplete strategy% (6367)------------------------------
% 0.22/0.52  % (6367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6367)Memory used [KB]: 10618
% 0.22/0.52  % (6367)Time elapsed: 0.097 s
% 0.22/0.52  % (6367)------------------------------
% 0.22/0.52  % (6367)------------------------------
% 0.22/0.52  % (6351)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.29/0.52  % (6356)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.29/0.53  % (6365)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.44/0.55  % (6349)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.56  % (6350)Refutation not found, incomplete strategy% (6350)------------------------------
% 1.44/0.56  % (6350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (6350)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (6350)Memory used [KB]: 11513
% 1.44/0.56  % (6350)Time elapsed: 0.134 s
% 1.44/0.56  % (6350)------------------------------
% 1.44/0.56  % (6350)------------------------------
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f1247,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f100,f237,f506,f524,f606,f622,f638,f682,f824,f929,f981,f1072,f1121,f1202,f1220,f1229,f1237,f1242,f1246])).
% 1.44/0.56  fof(f1246,plain,(
% 1.44/0.56    spl10_15 | spl10_16 | spl10_17 | spl10_18 | spl10_4 | ~spl10_31),
% 1.44/0.56    inference(avatar_split_clause,[],[f1245,f504,f98,f232,f229,f226,f223])).
% 1.44/0.56  fof(f223,plain,(
% 1.44/0.56    spl10_15 <=> k1_xboole_0 = sK0),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.44/0.56  fof(f226,plain,(
% 1.44/0.56    spl10_16 <=> k1_xboole_0 = sK1),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.44/0.56  fof(f229,plain,(
% 1.44/0.56    spl10_17 <=> k1_xboole_0 = sK2),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.44/0.56  fof(f232,plain,(
% 1.44/0.56    spl10_18 <=> k1_xboole_0 = sK3),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    spl10_4 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.44/0.56  fof(f504,plain,(
% 1.44/0.56    spl10_31 <=> m1_subset_1(k2_mcart_1(sK8),sK7)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 1.44/0.56  fof(f1245,plain,(
% 1.44/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl10_4 | ~spl10_31)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1244,f51])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f36,f35,f34,f33,f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(flattening,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 1.44/0.56    inference(negated_conjecture,[],[f16])).
% 1.44/0.56  fof(f16,conjecture,(
% 1.44/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).
% 1.44/0.56  fof(f1244,plain,(
% 1.44/0.56    ~m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl10_4 | ~spl10_31)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1243,f789])).
% 1.44/0.56  fof(f789,plain,(
% 1.44/0.56    r2_hidden(k2_mcart_1(sK8),sK7) | ~spl10_31),
% 1.44/0.56    inference(subsumption_resolution,[],[f787,f271])).
% 1.44/0.56  fof(f271,plain,(
% 1.44/0.56    ~v1_xboole_0(sK7)),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f269])).
% 1.44/0.56  fof(f269,plain,(
% 1.44/0.56    ~v1_xboole_0(sK7) | ~v1_xboole_0(sK7)),
% 1.44/0.56    inference(superposition,[],[f104,f156])).
% 1.44/0.56  fof(f156,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X1,X2,X3,X0) = X0 | ~v1_xboole_0(X0)) )),
% 1.44/0.56    inference(superposition,[],[f84,f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 1.44/0.56  fof(f84,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0)) )),
% 1.44/0.56    inference(equality_resolution,[],[f74])).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.56    inference(flattening,[],[f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.44/0.56    inference(nnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.44/0.56  fof(f104,plain,(
% 1.44/0.56    ~v1_xboole_0(k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.44/0.56    inference(resolution,[],[f56,f52])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.56    inference(rectify,[],[f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.56    inference(nnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.56  fof(f787,plain,(
% 1.44/0.56    r2_hidden(k2_mcart_1(sK8),sK7) | v1_xboole_0(sK7) | ~spl10_31),
% 1.44/0.56    inference(resolution,[],[f505,f58])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.44/0.56    inference(nnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.44/0.56  fof(f505,plain,(
% 1.44/0.56    m1_subset_1(k2_mcart_1(sK8),sK7) | ~spl10_31),
% 1.44/0.56    inference(avatar_component_clause,[],[f504])).
% 1.44/0.56  fof(f1243,plain,(
% 1.44/0.56    ~r2_hidden(k2_mcart_1(sK8),sK7) | ~m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_4),
% 1.44/0.56    inference(superposition,[],[f99,f78])).
% 1.44/0.56  fof(f78,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.44/0.56    inference(ennf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,axiom,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.44/0.56  fof(f99,plain,(
% 1.44/0.56    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | spl10_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f98])).
% 1.44/0.56  fof(f1242,plain,(
% 1.44/0.56    spl10_15 | spl10_16 | spl10_17 | spl10_18 | spl10_3 | ~spl10_46),
% 1.44/0.56    inference(avatar_split_clause,[],[f1241,f822,f95,f232,f229,f226,f223])).
% 1.44/0.56  fof(f95,plain,(
% 1.44/0.56    spl10_3 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.44/0.56  fof(f822,plain,(
% 1.44/0.56    spl10_46 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 1.44/0.56  fof(f1241,plain,(
% 1.44/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl10_3 | ~spl10_46)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1240,f51])).
% 1.44/0.56  fof(f1240,plain,(
% 1.44/0.56    ~m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl10_3 | ~spl10_46)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1239,f1212])).
% 1.44/0.56  fof(f1212,plain,(
% 1.44/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~spl10_46),
% 1.44/0.56    inference(subsumption_resolution,[],[f1210,f294])).
% 1.44/0.56  fof(f294,plain,(
% 1.44/0.56    ~v1_xboole_0(sK6)),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f292])).
% 1.44/0.56  fof(f292,plain,(
% 1.44/0.56    ~v1_xboole_0(sK6) | ~v1_xboole_0(sK6)),
% 1.44/0.56    inference(superposition,[],[f104,f157])).
% 1.44/0.56  fof(f157,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X1,X2,X0,X3) = X0 | ~v1_xboole_0(X0)) )),
% 1.44/0.56    inference(superposition,[],[f85,f55])).
% 1.44/0.56  fof(f85,plain,(
% 1.44/0.56    ( ! [X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3)) )),
% 1.44/0.56    inference(equality_resolution,[],[f73])).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f46])).
% 1.44/0.56  fof(f1210,plain,(
% 1.44/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | v1_xboole_0(sK6) | ~spl10_46),
% 1.44/0.56    inference(resolution,[],[f823,f58])).
% 1.44/0.56  fof(f823,plain,(
% 1.44/0.56    m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~spl10_46),
% 1.44/0.56    inference(avatar_component_clause,[],[f822])).
% 1.44/0.56  fof(f1239,plain,(
% 1.44/0.56    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_3),
% 1.44/0.56    inference(superposition,[],[f96,f77])).
% 1.44/0.56  fof(f77,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  fof(f96,plain,(
% 1.44/0.56    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | spl10_3),
% 1.44/0.56    inference(avatar_component_clause,[],[f95])).
% 1.44/0.56  fof(f1237,plain,(
% 1.44/0.56    ~spl10_57 | spl10_58),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f1236])).
% 1.44/0.56  fof(f1236,plain,(
% 1.44/0.56    $false | (~spl10_57 | spl10_58)),
% 1.44/0.56    inference(subsumption_resolution,[],[f1235,f319])).
% 1.44/0.56  fof(f319,plain,(
% 1.44/0.56    ~v1_xboole_0(sK5)),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f317])).
% 1.44/0.56  fof(f317,plain,(
% 1.44/0.56    ~v1_xboole_0(sK5) | ~v1_xboole_0(sK5)),
% 1.44/0.56    inference(superposition,[],[f104,f158])).
% 1.44/0.56  fof(f158,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X1,X0,X2,X3) = X0 | ~v1_xboole_0(X0)) )),
% 1.44/0.56    inference(superposition,[],[f86,f55])).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    ( ! [X2,X0,X3] : (k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3)) )),
% 1.44/0.56    inference(equality_resolution,[],[f72])).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f46])).
% 1.44/0.57  fof(f1235,plain,(
% 1.44/0.57    v1_xboole_0(sK5) | (~spl10_57 | spl10_58)),
% 1.44/0.57    inference(subsumption_resolution,[],[f1233,f1228])).
% 1.44/0.57  fof(f1228,plain,(
% 1.44/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | spl10_58),
% 1.44/0.57    inference(avatar_component_clause,[],[f1227])).
% 1.44/0.57  fof(f1227,plain,(
% 1.44/0.57    spl10_58 <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 1.44/0.57  fof(f1233,plain,(
% 1.44/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | v1_xboole_0(sK5) | ~spl10_57),
% 1.44/0.57    inference(resolution,[],[f1201,f58])).
% 1.44/0.57  fof(f1201,plain,(
% 1.44/0.57    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~spl10_57),
% 1.44/0.57    inference(avatar_component_clause,[],[f1200])).
% 1.44/0.57  fof(f1200,plain,(
% 1.44/0.57    spl10_57 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 1.44/0.57  fof(f1229,plain,(
% 1.44/0.57    spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_58 | spl10_2),
% 1.44/0.57    inference(avatar_split_clause,[],[f1225,f92,f1227,f232,f229,f226,f223])).
% 1.44/0.57  fof(f92,plain,(
% 1.44/0.57    spl10_2 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.44/0.57  fof(f1225,plain,(
% 1.44/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_2),
% 1.44/0.57    inference(subsumption_resolution,[],[f1224,f51])).
% 1.44/0.57  fof(f1224,plain,(
% 1.44/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_2),
% 1.44/0.57    inference(superposition,[],[f93,f76])).
% 1.44/0.57  fof(f76,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f27])).
% 1.44/0.57  fof(f93,plain,(
% 1.44/0.57    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | spl10_2),
% 1.44/0.57    inference(avatar_component_clause,[],[f92])).
% 1.44/0.57  fof(f1220,plain,(
% 1.44/0.57    spl10_19 | ~spl10_55),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f1219])).
% 1.44/0.57  fof(f1219,plain,(
% 1.44/0.57    $false | (spl10_19 | ~spl10_55)),
% 1.44/0.57    inference(subsumption_resolution,[],[f1218,f346])).
% 1.44/0.57  fof(f346,plain,(
% 1.44/0.57    ~v1_xboole_0(sK4)),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f344])).
% 1.44/0.57  fof(f344,plain,(
% 1.44/0.57    ~v1_xboole_0(sK4) | ~v1_xboole_0(sK4)),
% 1.44/0.57    inference(superposition,[],[f104,f159])).
% 1.44/0.57  fof(f159,plain,(
% 1.44/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = X0 | ~v1_xboole_0(X0)) )),
% 1.44/0.57    inference(superposition,[],[f87,f55])).
% 1.44/0.57  fof(f87,plain,(
% 1.44/0.57    ( ! [X2,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3)) )),
% 1.44/0.57    inference(equality_resolution,[],[f71])).
% 1.44/0.57  fof(f71,plain,(
% 1.44/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f46])).
% 1.44/0.57  fof(f1218,plain,(
% 1.44/0.57    v1_xboole_0(sK4) | (spl10_19 | ~spl10_55)),
% 1.44/0.57    inference(subsumption_resolution,[],[f1216,f236])).
% 1.44/0.57  fof(f236,plain,(
% 1.44/0.57    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | spl10_19),
% 1.44/0.57    inference(avatar_component_clause,[],[f235])).
% 1.44/0.57  fof(f235,plain,(
% 1.44/0.57    spl10_19 <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.44/0.57  fof(f1216,plain,(
% 1.44/0.57    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | v1_xboole_0(sK4) | ~spl10_55),
% 1.44/0.57    inference(resolution,[],[f1071,f58])).
% 1.44/0.57  fof(f1071,plain,(
% 1.44/0.57    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | ~spl10_55),
% 1.44/0.57    inference(avatar_component_clause,[],[f1070])).
% 1.44/0.57  fof(f1070,plain,(
% 1.44/0.57    spl10_55 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 1.44/0.57  fof(f1202,plain,(
% 1.44/0.57    spl10_27 | spl10_28 | spl10_29 | spl10_30 | spl10_57),
% 1.44/0.57    inference(avatar_split_clause,[],[f1180,f1200,f501,f498,f495,f492])).
% 1.44/0.57  fof(f492,plain,(
% 1.44/0.57    spl10_27 <=> k1_xboole_0 = sK4),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 1.44/0.57  fof(f495,plain,(
% 1.44/0.57    spl10_28 <=> k1_xboole_0 = sK5),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 1.44/0.57  fof(f498,plain,(
% 1.44/0.57    spl10_29 <=> k1_xboole_0 = sK6),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 1.44/0.57  fof(f501,plain,(
% 1.44/0.57    spl10_30 <=> k1_xboole_0 = sK7),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 1.44/0.57  fof(f1180,plain,(
% 1.44/0.57    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 1.44/0.57    inference(resolution,[],[f239,f106])).
% 1.44/0.57  fof(f106,plain,(
% 1.44/0.57    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.44/0.57    inference(resolution,[],[f101,f52])).
% 1.44/0.57  fof(f101,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.44/0.57    inference(subsumption_resolution,[],[f59,f56])).
% 1.44/0.57  fof(f59,plain,(
% 1.44/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f42])).
% 1.44/0.57  fof(f239,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f238])).
% 1.44/0.57  fof(f238,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(superposition,[],[f82,f76])).
% 1.44/0.57  fof(f82,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f31])).
% 1.44/0.57  fof(f31,plain,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.44/0.57    inference(ennf_transformation,[],[f13])).
% 1.44/0.57  fof(f13,axiom,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 1.44/0.57  fof(f1121,plain,(
% 1.44/0.57    ~spl10_18),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f1120])).
% 1.44/0.57  fof(f1120,plain,(
% 1.44/0.57    $false | ~spl10_18),
% 1.44/0.57    inference(subsumption_resolution,[],[f1106,f244])).
% 1.44/0.57  fof(f244,plain,(
% 1.44/0.57    v1_xboole_0(k1_xboole_0)),
% 1.44/0.57    inference(resolution,[],[f187,f57])).
% 1.44/0.57  fof(f57,plain,(
% 1.44/0.57    ( ! [X0] : (r2_hidden(sK9(X0),X0) | v1_xboole_0(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f41])).
% 1.44/0.57  fof(f187,plain,(
% 1.44/0.57    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.44/0.57    inference(subsumption_resolution,[],[f183,f182])).
% 1.44/0.57  fof(f182,plain,(
% 1.44/0.57    ( ! [X4] : (k1_xboole_0 != k1_tarski(X4)) )),
% 1.44/0.57    inference(subsumption_resolution,[],[f181,f176])).
% 1.44/0.57  fof(f176,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_xboole_0 != k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f175])).
% 1.44/0.57  fof(f175,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_xboole_0 != k1_tarski(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(superposition,[],[f66,f65])).
% 1.44/0.57  fof(f65,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f43])).
% 1.44/0.57  fof(f43,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.44/0.57    inference(nnf_transformation,[],[f5])).
% 1.44/0.57  fof(f5,axiom,(
% 1.44/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.44/0.57  fof(f66,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f44])).
% 1.44/0.57  fof(f44,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.44/0.57    inference(nnf_transformation,[],[f7])).
% 1.44/0.57  fof(f7,axiom,(
% 1.44/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.44/0.57  fof(f181,plain,(
% 1.44/0.57    ( ! [X4,X5] : (k1_xboole_0 != k1_tarski(X4) | r2_hidden(X4,X5)) )),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f180])).
% 1.44/0.57  fof(f180,plain,(
% 1.44/0.57    ( ! [X4,X5] : (k1_xboole_0 != k1_tarski(X4) | r2_hidden(X4,X5) | r2_hidden(X4,X5)) )),
% 1.44/0.57    inference(superposition,[],[f64,f67])).
% 1.44/0.57  fof(f67,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f44])).
% 1.44/0.57  fof(f64,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f43])).
% 1.44/0.57  fof(f183,plain,(
% 1.44/0.57    ( ! [X2] : (k1_xboole_0 = k1_tarski(X2) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.44/0.57    inference(superposition,[],[f83,f54])).
% 1.44/0.57  fof(f54,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f3])).
% 1.44/0.57  fof(f3,axiom,(
% 1.44/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.44/0.57  fof(f83,plain,(
% 1.44/0.57    ( ! [X2,X1] : (k1_tarski(X2) = k3_xboole_0(k2_tarski(X2,X2),X1) | ~r2_hidden(X2,X1)) )),
% 1.44/0.57    inference(equality_resolution,[],[f69])).
% 1.44/0.57  fof(f69,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f26])).
% 1.44/0.57  fof(f26,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.44/0.57    inference(flattening,[],[f25])).
% 1.44/0.57  fof(f25,plain,(
% 1.44/0.57    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 1.44/0.57    inference(ennf_transformation,[],[f6])).
% 1.44/0.57  fof(f6,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 1.44/0.57  fof(f1106,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_18),
% 1.44/0.57    inference(backward_demodulation,[],[f271,f1101])).
% 1.44/0.57  fof(f1101,plain,(
% 1.44/0.57    k1_xboole_0 = sK7 | ~spl10_18),
% 1.44/0.57    inference(resolution,[],[f1079,f172])).
% 1.44/0.57  fof(f172,plain,(
% 1.44/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(superposition,[],[f62,f54])).
% 1.44/0.57  fof(f62,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f23])).
% 1.44/0.57  fof(f23,plain,(
% 1.44/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.57    inference(ennf_transformation,[],[f2])).
% 1.44/0.57  fof(f2,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.57  fof(f1079,plain,(
% 1.44/0.57    r1_tarski(sK7,k1_xboole_0) | ~spl10_18),
% 1.44/0.57    inference(backward_demodulation,[],[f154,f233])).
% 1.44/0.57  fof(f233,plain,(
% 1.44/0.57    k1_xboole_0 = sK3 | ~spl10_18),
% 1.44/0.57    inference(avatar_component_clause,[],[f232])).
% 1.44/0.57  fof(f154,plain,(
% 1.44/0.57    r1_tarski(sK7,sK3)),
% 1.44/0.57    inference(resolution,[],[f63,f50])).
% 1.44/0.57  fof(f50,plain,(
% 1.44/0.57    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 1.44/0.57    inference(cnf_transformation,[],[f37])).
% 1.44/0.57  fof(f63,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f24])).
% 1.44/0.57  fof(f24,plain,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.44/0.57    inference(ennf_transformation,[],[f18])).
% 1.44/0.57  fof(f18,plain,(
% 1.44/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.44/0.57    inference(unused_predicate_definition_removal,[],[f9])).
% 1.44/0.57  fof(f9,axiom,(
% 1.44/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.57  fof(f1072,plain,(
% 1.44/0.57    spl10_27 | spl10_28 | spl10_29 | spl10_30 | spl10_55),
% 1.44/0.57    inference(avatar_split_clause,[],[f1050,f1070,f501,f498,f495,f492])).
% 1.44/0.57  fof(f1050,plain,(
% 1.44/0.57    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 1.44/0.57    inference(resolution,[],[f220,f106])).
% 1.44/0.57  fof(f220,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f219])).
% 1.44/0.57  fof(f219,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(superposition,[],[f81,f75])).
% 1.44/0.57  fof(f75,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f27])).
% 1.44/0.57  fof(f81,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f30,plain,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.44/0.57    inference(ennf_transformation,[],[f12])).
% 1.44/0.57  fof(f12,axiom,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).
% 1.44/0.57  fof(f981,plain,(
% 1.44/0.57    ~spl10_17),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f980])).
% 1.44/0.57  fof(f980,plain,(
% 1.44/0.57    $false | ~spl10_17),
% 1.44/0.57    inference(subsumption_resolution,[],[f967,f244])).
% 1.44/0.57  fof(f967,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_17),
% 1.44/0.57    inference(backward_demodulation,[],[f294,f962])).
% 1.44/0.57  fof(f962,plain,(
% 1.44/0.57    k1_xboole_0 = sK6 | ~spl10_17),
% 1.44/0.57    inference(resolution,[],[f935,f172])).
% 1.44/0.57  fof(f935,plain,(
% 1.44/0.57    r1_tarski(sK6,k1_xboole_0) | ~spl10_17),
% 1.44/0.57    inference(backward_demodulation,[],[f153,f230])).
% 1.44/0.57  fof(f230,plain,(
% 1.44/0.57    k1_xboole_0 = sK2 | ~spl10_17),
% 1.44/0.57    inference(avatar_component_clause,[],[f229])).
% 1.44/0.57  fof(f153,plain,(
% 1.44/0.57    r1_tarski(sK6,sK2)),
% 1.44/0.57    inference(resolution,[],[f63,f49])).
% 1.44/0.57  fof(f49,plain,(
% 1.44/0.57    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 1.44/0.57    inference(cnf_transformation,[],[f37])).
% 1.44/0.57  fof(f929,plain,(
% 1.44/0.57    ~spl10_16),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f928])).
% 1.44/0.57  fof(f928,plain,(
% 1.44/0.57    $false | ~spl10_16),
% 1.44/0.57    inference(subsumption_resolution,[],[f916,f244])).
% 1.44/0.57  fof(f916,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_16),
% 1.44/0.57    inference(backward_demodulation,[],[f319,f911])).
% 1.44/0.57  fof(f911,plain,(
% 1.44/0.57    k1_xboole_0 = sK5 | ~spl10_16),
% 1.44/0.57    inference(resolution,[],[f888,f172])).
% 1.44/0.57  fof(f888,plain,(
% 1.44/0.57    r1_tarski(sK5,k1_xboole_0) | ~spl10_16),
% 1.44/0.57    inference(backward_demodulation,[],[f152,f227])).
% 1.44/0.57  fof(f227,plain,(
% 1.44/0.57    k1_xboole_0 = sK1 | ~spl10_16),
% 1.44/0.57    inference(avatar_component_clause,[],[f226])).
% 1.44/0.57  fof(f152,plain,(
% 1.44/0.57    r1_tarski(sK5,sK1)),
% 1.44/0.57    inference(resolution,[],[f63,f48])).
% 1.44/0.57  fof(f48,plain,(
% 1.44/0.57    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 1.44/0.57    inference(cnf_transformation,[],[f37])).
% 1.44/0.57  fof(f824,plain,(
% 1.44/0.57    spl10_27 | spl10_28 | spl10_29 | spl10_30 | spl10_46),
% 1.44/0.57    inference(avatar_split_clause,[],[f802,f822,f501,f498,f495,f492])).
% 1.44/0.57  fof(f802,plain,(
% 1.44/0.57    m1_subset_1(k2_mcart_1(k1_mcart_1(sK8)),sK6) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 1.44/0.57    inference(resolution,[],[f215,f106])).
% 1.44/0.57  fof(f215,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f214])).
% 1.44/0.57  fof(f214,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X4)),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(superposition,[],[f79,f77])).
% 1.44/0.57  fof(f79,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f28])).
% 1.44/0.57  fof(f28,plain,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.44/0.57    inference(ennf_transformation,[],[f10])).
% 1.44/0.57  fof(f10,axiom,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).
% 1.44/0.57  fof(f682,plain,(
% 1.44/0.57    ~spl10_15),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f681])).
% 1.44/0.57  fof(f681,plain,(
% 1.44/0.57    $false | ~spl10_15),
% 1.44/0.57    inference(subsumption_resolution,[],[f667,f244])).
% 1.44/0.57  fof(f667,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_15),
% 1.44/0.57    inference(backward_demodulation,[],[f346,f661])).
% 1.44/0.57  fof(f661,plain,(
% 1.44/0.57    k1_xboole_0 = sK4 | ~spl10_15),
% 1.44/0.57    inference(resolution,[],[f588,f172])).
% 1.44/0.57  fof(f588,plain,(
% 1.44/0.57    r1_tarski(sK4,k1_xboole_0) | ~spl10_15),
% 1.44/0.57    inference(forward_demodulation,[],[f151,f224])).
% 1.44/0.57  fof(f224,plain,(
% 1.44/0.57    k1_xboole_0 = sK0 | ~spl10_15),
% 1.44/0.57    inference(avatar_component_clause,[],[f223])).
% 1.44/0.57  fof(f151,plain,(
% 1.44/0.57    r1_tarski(sK4,sK0)),
% 1.44/0.57    inference(resolution,[],[f63,f47])).
% 1.44/0.57  fof(f47,plain,(
% 1.44/0.57    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(cnf_transformation,[],[f37])).
% 1.44/0.57  fof(f638,plain,(
% 1.44/0.57    ~spl10_30),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f637])).
% 1.44/0.57  fof(f637,plain,(
% 1.44/0.57    $false | ~spl10_30),
% 1.44/0.57    inference(subsumption_resolution,[],[f629,f244])).
% 1.44/0.57  fof(f629,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_30),
% 1.44/0.57    inference(backward_demodulation,[],[f271,f502])).
% 1.44/0.57  fof(f502,plain,(
% 1.44/0.57    k1_xboole_0 = sK7 | ~spl10_30),
% 1.44/0.57    inference(avatar_component_clause,[],[f501])).
% 1.44/0.57  fof(f622,plain,(
% 1.44/0.57    ~spl10_29),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f621])).
% 1.44/0.57  fof(f621,plain,(
% 1.44/0.57    $false | ~spl10_29),
% 1.44/0.57    inference(subsumption_resolution,[],[f613,f244])).
% 1.44/0.57  fof(f613,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_29),
% 1.44/0.57    inference(backward_demodulation,[],[f294,f499])).
% 1.44/0.57  fof(f499,plain,(
% 1.44/0.57    k1_xboole_0 = sK6 | ~spl10_29),
% 1.44/0.57    inference(avatar_component_clause,[],[f498])).
% 1.44/0.57  fof(f606,plain,(
% 1.44/0.57    ~spl10_28),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f605])).
% 1.44/0.57  fof(f605,plain,(
% 1.44/0.57    $false | ~spl10_28),
% 1.44/0.57    inference(subsumption_resolution,[],[f597,f244])).
% 1.44/0.57  fof(f597,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_28),
% 1.44/0.57    inference(backward_demodulation,[],[f319,f496])).
% 1.44/0.57  fof(f496,plain,(
% 1.44/0.57    k1_xboole_0 = sK5 | ~spl10_28),
% 1.44/0.57    inference(avatar_component_clause,[],[f495])).
% 1.44/0.57  fof(f524,plain,(
% 1.44/0.57    ~spl10_27),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f523])).
% 1.44/0.57  fof(f523,plain,(
% 1.44/0.57    $false | ~spl10_27),
% 1.44/0.57    inference(subsumption_resolution,[],[f515,f244])).
% 1.44/0.57  fof(f515,plain,(
% 1.44/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl10_27),
% 1.44/0.57    inference(backward_demodulation,[],[f346,f493])).
% 1.44/0.57  fof(f493,plain,(
% 1.44/0.57    k1_xboole_0 = sK4 | ~spl10_27),
% 1.44/0.57    inference(avatar_component_clause,[],[f492])).
% 1.44/0.57  fof(f506,plain,(
% 1.44/0.57    spl10_27 | spl10_28 | spl10_29 | spl10_30 | spl10_31),
% 1.44/0.57    inference(avatar_split_clause,[],[f472,f504,f501,f498,f495,f492])).
% 1.44/0.57  fof(f472,plain,(
% 1.44/0.57    m1_subset_1(k2_mcart_1(sK8),sK7) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 1.44/0.57    inference(resolution,[],[f213,f106])).
% 1.44/0.57  fof(f213,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k2_mcart_1(X4),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(duplicate_literal_removal,[],[f212])).
% 1.44/0.57  fof(f212,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(superposition,[],[f80,f78])).
% 1.44/0.57  fof(f80,plain,(
% 1.44/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f29])).
% 1.44/0.57  fof(f29,plain,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.44/0.57    inference(ennf_transformation,[],[f11])).
% 1.44/0.57  fof(f11,axiom,(
% 1.44/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).
% 1.44/0.57  fof(f237,plain,(
% 1.44/0.57    spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_19 | spl10_1),
% 1.44/0.57    inference(avatar_split_clause,[],[f221,f89,f235,f232,f229,f226,f223])).
% 1.44/0.57  fof(f89,plain,(
% 1.44/0.57    spl10_1 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.44/0.57  fof(f221,plain,(
% 1.44/0.57    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_1),
% 1.44/0.57    inference(subsumption_resolution,[],[f218,f51])).
% 1.44/0.57  fof(f218,plain,(
% 1.44/0.57    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | ~m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_1),
% 1.44/0.57    inference(superposition,[],[f90,f75])).
% 1.44/0.57  fof(f90,plain,(
% 1.44/0.57    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | spl10_1),
% 1.44/0.57    inference(avatar_component_clause,[],[f89])).
% 1.44/0.57  fof(f100,plain,(
% 1.44/0.57    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 1.44/0.57    inference(avatar_split_clause,[],[f53,f98,f95,f92,f89])).
% 1.44/0.57  fof(f53,plain,(
% 1.44/0.57    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 1.44/0.57    inference(cnf_transformation,[],[f37])).
% 1.44/0.57  % SZS output end Proof for theBenchmark
% 1.44/0.57  % (6349)------------------------------
% 1.44/0.57  % (6349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (6349)Termination reason: Refutation
% 1.44/0.57  
% 1.44/0.57  % (6349)Memory used [KB]: 11257
% 1.44/0.57  % (6349)Time elapsed: 0.117 s
% 1.44/0.57  % (6349)------------------------------
% 1.44/0.57  % (6349)------------------------------
% 1.44/0.58  % (6346)Success in time 0.208 s
%------------------------------------------------------------------------------
