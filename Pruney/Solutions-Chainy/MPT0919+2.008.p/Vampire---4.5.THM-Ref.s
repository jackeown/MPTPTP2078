%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 124 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 (1042 expanded)
%              Number of equality atoms :   86 ( 581 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f77,f90,f103,f109,f114])).

fof(f114,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f34,f30,f31,f32,f24,f54,f19])).

fof(f19,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X6
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
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
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
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
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f54,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_5
  <=> sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f24,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f18,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(resolution,[],[f18,f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f30,plain,(
    m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(resolution,[],[f18,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f34,plain,(
    m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(resolution,[],[f18,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f109,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f107,f52,f48,f44,f40,f36])).

fof(f36,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f40,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f44,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f48,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f107,plain,
    ( sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f103,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f20,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f23,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f23,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f22,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f21,f42])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31630)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (31630)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (31620)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (31638)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f64,f77,f90,f103,f109,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ~spl6_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    $false | ~spl6_5),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f34,f30,f31,f32,f24,f54,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X6 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl6_5 <=> sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.20/0.48    inference(resolution,[],[f18,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.20/0.48    inference(resolution,[],[f18,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.20/0.48    inference(resolution,[],[f18,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.20/0.48    inference(resolution,[],[f18,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl6_1 | spl6_2 | spl6_3 | spl6_4 | spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f52,f48,f44,f40,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    spl6_1 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl6_2 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    spl6_3 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl6_4 <=> k1_xboole_0 = sK3),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.48    inference(resolution,[],[f18,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~spl6_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    $false | ~spl6_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f20,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f36])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~spl6_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    $false | ~spl6_4),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f23,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | ~spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    k1_xboole_0 != sK3),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~spl6_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    $false | ~spl6_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f44])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    k1_xboole_0 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ~spl6_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    $false | ~spl6_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f21,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f40])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (31630)------------------------------
% 0.20/0.48  % (31630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31630)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (31630)Memory used [KB]: 6140
% 0.20/0.48  % (31630)Time elapsed: 0.056 s
% 0.20/0.48  % (31630)------------------------------
% 0.20/0.48  % (31630)------------------------------
% 0.20/0.48  % (31619)Success in time 0.121 s
%------------------------------------------------------------------------------
