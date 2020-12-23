%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 471 expanded)
%              Number of leaves         :    6 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  258 (4174 expanded)
%              Number of equality atoms :  158 (2448 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f126,f222])).

fof(f222,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f73,f218])).

fof(f218,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | ~ spl14_2 ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK4,sK1)
    | ~ spl14_2 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK4,sK1)
    | sK4 != sK4
    | ~ spl14_2 ),
    inference(superposition,[],[f51,f198])).

fof(f198,plain,
    ( sK4 = sK7(sK5,sK4)
    | ~ spl14_2 ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( sK5 != sK5
    | sK4 = sK7(sK5,sK4)
    | ~ spl14_2 ),
    inference(superposition,[],[f136,f78])).

fof(f78,plain,
    ( sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f76])).

% (21801)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f76,plain,
    ( spl14_2
  <=> sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f136,plain,(
    ! [X10,X8,X11,X9] :
      ( sK5 != k4_mcart_1(X8,X9,X10,X11)
      | sK4 = X9 ) ),
    inference(superposition,[],[f27,f117])).

fof(f117,plain,(
    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK4,sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) ),
    inference(backward_demodulation,[],[f44,f116])).

fof(f116,plain,(
    sK4 = sK11(sK0,sK1,sK2,sK3,sK5) ),
    inference(global_subsumption,[],[f43,f45,f46,f47,f115])).

fof(f115,plain,
    ( ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK11(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK11(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f11,f44])).

fof(f11,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X7 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f47,plain,(
    m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(resolution,[],[f12,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f12,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f37])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(resolution,[],[f12,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK11(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f36])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(resolution,[],[f12,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK12(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f34])).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(resolution,[],[f12,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK13(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f35])).

fof(f35,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f12,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f51,plain,(
    ! [X1] :
      ( sK7(sK5,X1) != X1
      | ~ m1_subset_1(X1,sK1)
      | sK4 != X1 ) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f12,f49])).

fof(f49,plain,(
    ! [X1] :
      ( sK4 != X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(X1,sK1)
      | sK7(sK5,X1) != X1 ) ),
    inference(superposition,[],[f17,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X1)
      | sK7(X4,X5) != X5
      | k9_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f8])).

% (21812)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_mcart_1)).

fof(f17,plain,(
    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl14_1
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f126,plain,(
    spl14_1 ),
    inference(avatar_split_clause,[],[f122,f72])).

fof(f122,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(global_subsumption,[],[f118])).

fof(f118,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(backward_demodulation,[],[f46,f116])).

fof(f79,plain,
    ( ~ spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f70,f76,f72])).

fof(f70,plain,
    ( sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4))
    | ~ m1_subset_1(sK4,sK1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( sK4 != X0
      | sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(global_subsumption,[],[f13,f14,f15,f16,f12,f48])).

fof(f48,plain,(
    ! [X0] :
      ( sK4 != X0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(X0,sK1)
      | sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) ) ),
    inference(superposition,[],[f17,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X1)
      | k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (21803)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (21811)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (21794)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (21811)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f79,f126,f222])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    ~spl14_1 | ~spl14_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f220])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    $false | (~spl14_1 | ~spl14_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f73,f218])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    ~m1_subset_1(sK4,sK1) | ~spl14_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f217])).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    sK4 != sK4 | ~m1_subset_1(sK4,sK1) | ~spl14_2),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    sK4 != sK4 | ~m1_subset_1(sK4,sK1) | sK4 != sK4 | ~spl14_2),
% 0.20/0.49    inference(superposition,[],[f51,f198])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    sK4 = sK7(sK5,sK4) | ~spl14_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f197])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    sK5 != sK5 | sK4 = sK7(sK5,sK4) | ~spl14_2),
% 0.20/0.49    inference(superposition,[],[f136,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4)) | ~spl14_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  % (21801)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl14_2 <=> sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ( ! [X10,X8,X11,X9] : (sK5 != k4_mcart_1(X8,X9,X10,X11) | sK4 = X9) )),
% 0.20/0.50    inference(superposition,[],[f27,f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK4,sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.50    inference(backward_demodulation,[],[f44,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    sK4 = sK11(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.50    inference(global_subsumption,[],[f43,f45,f46,f47,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK11(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    sK5 != sK5 | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK11(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.50    inference(superposition,[],[f11,f44])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X7) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.50    inference(flattening,[],[f6])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f4])).
% 0.20/0.50  fof(f4,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.20/0.50    inference(global_subsumption,[],[f13,f14,f15,f16,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.20/0.50    inference(resolution,[],[f12,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    k1_xboole_0 != sK3),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    k1_xboole_0 != sK2),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    k1_xboole_0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    k1_xboole_0 != sK0),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.20/0.50    inference(global_subsumption,[],[f13,f14,f15,f16,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.20/0.50    inference(resolution,[],[f12,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK11(X0,X1,X2,X3,X4),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.20/0.50    inference(global_subsumption,[],[f13,f14,f15,f16,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.20/0.50    inference(resolution,[],[f12,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK12(X0,X1,X2,X3,X4),X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.20/0.50    inference(global_subsumption,[],[f13,f14,f15,f16,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.20/0.50    inference(resolution,[],[f12,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK13(X0,X1,X2,X3,X4),X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.50    inference(global_subsumption,[],[f13,f14,f15,f16,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.50    inference(resolution,[],[f12,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X1 = X5) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X1] : (sK7(sK5,X1) != X1 | ~m1_subset_1(X1,sK1) | sK4 != X1) )),
% 0.20/0.50    inference(global_subsumption,[],[f13,f14,f15,f16,f12,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X1] : (sK4 != X1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(X1,sK1) | sK7(sK5,X1) != X1) )),
% 0.20/0.50    inference(superposition,[],[f17,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(X5,X1) | sK7(X4,X5) != X5 | k9_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  % (21812)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X1) => (k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X7)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_mcart_1)).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    m1_subset_1(sK4,sK1) | ~spl14_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl14_1 <=> m1_subset_1(sK4,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl14_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f122,f72])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    m1_subset_1(sK4,sK1)),
% 0.20/0.51    inference(global_subsumption,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    m1_subset_1(sK4,sK1)),
% 0.20/0.51    inference(backward_demodulation,[],[f46,f116])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ~spl14_1 | spl14_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f70,f76,f72])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4)) | ~m1_subset_1(sK4,sK1)),
% 0.20/0.51    inference(equality_resolution,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (sK4 != X0 | sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.51    inference(global_subsumption,[],[f13,f14,f15,f16,f12,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (sK4 != X0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(X0,sK1) | sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))) )),
% 0.20/0.51    inference(superposition,[],[f17,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(X5,X1) | k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (21811)------------------------------
% 0.20/0.51  % (21811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21811)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (21811)Memory used [KB]: 10874
% 0.20/0.51  % (21811)Time elapsed: 0.090 s
% 0.20/0.51  % (21811)------------------------------
% 0.20/0.51  % (21811)------------------------------
% 0.20/0.51  % (21790)Success in time 0.156 s
%------------------------------------------------------------------------------
