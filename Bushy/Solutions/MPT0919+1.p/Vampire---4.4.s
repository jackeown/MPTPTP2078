%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t79_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 131 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  247 ( 587 expanded)
%              Number of equality atoms :   83 ( 263 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f77,f84,f91,f98,f105,f130,f188,f191,f194,f197,f200])).

fof(f200,plain,
    ( ~ spl7_8
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f198,f90])).

fof(f90,plain,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_8
  <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f198,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl7_23 ),
    inference(resolution,[],[f187,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',dt_k9_mcart_1)).

fof(f187,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_23
  <=> ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f197,plain,
    ( ~ spl7_8
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f195,f90])).

fof(f195,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl7_21 ),
    inference(resolution,[],[f181,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',dt_k10_mcart_1)).

fof(f181,plain,
    ( ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl7_21
  <=> ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f194,plain,
    ( ~ spl7_8
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f192,f90])).

fof(f192,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl7_19 ),
    inference(resolution,[],[f175,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',dt_k11_mcart_1)).

fof(f175,plain,
    ( ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_19
  <=> ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f191,plain,
    ( ~ spl7_8
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f189,f90])).

fof(f189,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl7_17 ),
    inference(resolution,[],[f169,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',dt_k8_mcart_1)).

fof(f169,plain,
    ( ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_17
  <=> ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f188,plain,
    ( ~ spl7_17
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_23
    | spl7_11
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f133,f128,f96,f186,f180,f174,f168])).

fof(f96,plain,
    ( spl7_11
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f128,plain,
    ( spl7_14
  <=> k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f133,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f132,f97])).

fof(f97,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f132,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK4
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK4
    | ~ spl7_14 ),
    inference(superposition,[],[f37,f129])).

fof(f129,plain,
    ( k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f37,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X6 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',t79_mcart_1)).

fof(f130,plain,
    ( spl7_14
    | spl7_1
    | spl7_3
    | spl7_5
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f123,f89,f82,f75,f68,f61,f128])).

fof(f61,plain,
    ( spl7_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f68,plain,
    ( spl7_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f75,plain,
    ( spl7_5
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f82,plain,
    ( spl7_7
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f123,plain,
    ( k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f122,f62])).

fof(f62,plain,
    ( k1_xboole_0 != sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f122,plain,
    ( k1_xboole_0 = sK0
    | k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f121,f83])).

fof(f83,plain,
    ( k1_xboole_0 != sK3
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f121,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f120,f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK2
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f120,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f118,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | ~ spl7_8 ),
    inference(resolution,[],[f45,f90])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',t60_mcart_1)).

fof(f105,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f47,f103])).

fof(f103,plain,
    ( spl7_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f47,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t79_mcart_1.p',d2_xboole_0)).

fof(f98,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f38,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f39,f61])).

fof(f39,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
