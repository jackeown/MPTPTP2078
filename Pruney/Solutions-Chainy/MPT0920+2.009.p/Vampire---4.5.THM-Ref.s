%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 144 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 (1096 expanded)
%              Number of equality atoms :   72 ( 573 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f137,f143,f149,f155])).

fof(f155,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f151,f19])).

fof(f19,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X7
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X7 ) ) ) ) )
         => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f151,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | spl7_4 ),
    inference(resolution,[],[f130,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f130,plain,
    ( ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_4
  <=> m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f149,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f145,f19])).

fof(f145,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | spl7_3 ),
    inference(resolution,[],[f126,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f126,plain,
    ( ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_3
  <=> m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f143,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f139,f19])).

fof(f139,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(resolution,[],[f122,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f122,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_2
  <=> m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f137,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f133,f19])).

fof(f133,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | spl7_1 ),
    inference(resolution,[],[f118,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f118,plain,
    ( ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_1
  <=> m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f131,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f82,f128,f124,f120,f116])).

fof(f82,plain,
    ( ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f36,plain,(
    ~ sQ6_eqProxy(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(equality_proxy_replacement,[],[f25,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f25,plain,(
    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,
    ( sQ6_eqProxy(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sQ6_eqProxy(k4_mcart_1(X6,X7,X8,X9),sK5)
      | sQ6_eqProxy(sK4,X7)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(equality_proxy_replacement,[],[f20,f35,f35])).

fof(f20,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X7
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5) ),
    inference(subsumption_resolution,[],[f77,f40])).

fof(f40,plain,(
    ~ sQ6_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f21,f35])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,
    ( sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5)
    | sQ6_eqProxy(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f39,plain,(
    ~ sQ6_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f22,f35])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,
    ( sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5)
    | sQ6_eqProxy(k1_xboole_0,sK1)
    | sQ6_eqProxy(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f38,plain,(
    ~ sQ6_eqProxy(k1_xboole_0,sK2) ),
    inference(equality_proxy_replacement,[],[f23,f35])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,
    ( sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5)
    | sQ6_eqProxy(k1_xboole_0,sK2)
    | sQ6_eqProxy(k1_xboole_0,sK1)
    | sQ6_eqProxy(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f37,plain,(
    ~ sQ6_eqProxy(k1_xboole_0,sK3) ),
    inference(equality_proxy_replacement,[],[f24,f35])).

fof(f24,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5)
    | sQ6_eqProxy(k1_xboole_0,sK3)
    | sQ6_eqProxy(k1_xboole_0,sK2)
    | sQ6_eqProxy(k1_xboole_0,sK1)
    | sQ6_eqProxy(k1_xboole_0,sK0) ),
    inference(resolution,[],[f42,f19])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | sQ6_eqProxy(k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)),X4)
      | sQ6_eqProxy(k1_xboole_0,X3)
      | sQ6_eqProxy(k1_xboole_0,X2)
      | sQ6_eqProxy(k1_xboole_0,X1)
      | sQ6_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f35,f35,f35,f35,f35])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:09:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22973)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (22983)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (22973)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (22975)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (22981)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f131,f137,f143,f149,f155])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl7_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    $false | spl7_4),
% 0.22/0.48    inference(subsumption_resolution,[],[f151,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | spl7_4),
% 0.22/0.48    inference(resolution,[],[f130,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) | spl7_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f128])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl7_4 <=> m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    spl7_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f148])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    $false | spl7_3),
% 0.22/0.48    inference(subsumption_resolution,[],[f145,f19])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | spl7_3),
% 0.22/0.48    inference(resolution,[],[f126,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) | spl7_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl7_3 <=> m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl7_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    $false | spl7_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f139,f19])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 0.22/0.48    inference(resolution,[],[f122,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | spl7_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl7_2 <=> m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    spl7_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    $false | spl7_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f133,f19])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | spl7_1),
% 0.22/0.48    inference(resolution,[],[f118,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | spl7_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl7_1 <=> m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f82,f128,f124,f120,f116])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f79,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~sQ6_eqProxy(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f25,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    sQ6_eqProxy(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK5)) | ~m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.22/0.48    inference(resolution,[],[f78,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X6,X8,X7,X9] : (~sQ6_eqProxy(k4_mcart_1(X6,X7,X8,X9),sK5) | sQ6_eqProxy(sK4,X7) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f20,f35,f35])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X6,X8,X7,X9] : (sK4 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f77,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ~sQ6_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f21,f35])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    k1_xboole_0 != sK0),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5) | sQ6_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f76,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~sQ6_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f22,f35])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5) | sQ6_eqProxy(k1_xboole_0,sK1) | sQ6_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f75,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ~sQ6_eqProxy(k1_xboole_0,sK2)),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f23,f35])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    k1_xboole_0 != sK2),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5) | sQ6_eqProxy(k1_xboole_0,sK2) | sQ6_eqProxy(k1_xboole_0,sK1) | sQ6_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f73,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~sQ6_eqProxy(k1_xboole_0,sK3)),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f24,f35])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    k1_xboole_0 != sK3),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    sQ6_eqProxy(k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),sK5) | sQ6_eqProxy(k1_xboole_0,sK3) | sQ6_eqProxy(k1_xboole_0,sK2) | sQ6_eqProxy(k1_xboole_0,sK1) | sQ6_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.48    inference(resolution,[],[f42,f19])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | sQ6_eqProxy(k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)),X4) | sQ6_eqProxy(k1_xboole_0,X3) | sQ6_eqProxy(k1_xboole_0,X2) | sQ6_eqProxy(k1_xboole_0,X1) | sQ6_eqProxy(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f26,f35,f35,f35,f35,f35])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22973)------------------------------
% 0.22/0.48  % (22973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22973)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (22973)Memory used [KB]: 6140
% 0.22/0.48  % (22973)Time elapsed: 0.057 s
% 0.22/0.48  % (22973)------------------------------
% 0.22/0.48  % (22973)------------------------------
% 0.22/0.49  % (22967)Success in time 0.122 s
%------------------------------------------------------------------------------
